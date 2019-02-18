// need to put this in a separate package to dot import gocheck;
// List identifier conflicts
package filesys_test

import (
	"io/ioutil"
	"os"
	"sort"
	"testing"

	"github.com/tchajed/goose/machine/filesys"
)
import . "gopkg.in/check.v1"

func Test(t *testing.T) { TestingT(t) }

// FilesysSuite implements the actual filesystem test suite.
//
// It is not used as a gocheck suite but embedded in both MemFilesysSuite and
// DirFilesysSuite (we can't do this directly because gocheck uses the suite
// type as its name, so there would be no way to distinguish between the mem
// and dir suites)
type FilesysSuite struct {
	fs filesys.Filesys
}

func (s FilesysSuite) TestCreateReadExact(c *C) {
	written := []byte("some data")
	f := s.fs.Create("test.bin")
	s.fs.Append(f, written)
	s.fs.Close(f)

	f2 := s.fs.Open("test.bin")
	data := s.fs.ReadAt(f2, 0, uint64(len(written)))
	c.Check(data, DeepEquals, written)
}

func (s FilesysSuite) TestCreateReadExtra(c *C) {
	written := []byte("some data")
	f := s.fs.Create("test.bin")
	s.fs.Append(f, written)
	s.fs.Close(f)

	f2 := s.fs.Open("test.bin")
	data := s.fs.ReadAt(f2, 0, 4096)
	c.Check(data, DeepEquals, written)
}

func (s FilesysSuite) TestReadAtOffset(c *C) {
	written := []byte("some longer data")
	f := s.fs.Create("test.bin")
	s.fs.Append(f, written)
	s.fs.Close(f)

	f2 := s.fs.Open("test.bin")
	data := s.fs.ReadAt(f2, uint64(len("some ")), uint64(len("longer")))
	c.Check(data, DeepEquals, []byte("longer"))
}

// for checking directory listings in canonical order
func sorted(s []string) []string {
	sort.Slice(s, func(i, j int) bool {
		return s[i] < s[j]
	})
	return s
}

func (s FilesysSuite) TestList(c *C) {
	c.Check(s.fs.List(), HasLen, 0)
	s.fs.Close(s.fs.Create("f1"))
	s.fs.Close(s.fs.Create("f2"))
	c.Check(sorted(s.fs.List()), DeepEquals, []string{"f1", "f2"})
}

func (s FilesysSuite) TestDelete(c *C) {
	s.fs.Close(s.fs.Create("f1"))
	s.fs.Close(s.fs.Create("f2"))
	c.Check(sorted(s.fs.List()), DeepEquals, []string{"f1", "f2"})
	s.fs.Delete("f1")
	c.Check(sorted(s.fs.List()), DeepEquals, []string{"f2"})
}

func (s FilesysSuite) TestAtomicCreate(c *C) {
	contents := []byte("hello world")
	s.fs.AtomicCreate("testfile", contents)
	f := s.fs.Open("testfile")
	data := s.fs.ReadAt(f, 0, uint64(len(contents)))
	c.Check(data, DeepEquals, contents)
}

type MemFilesysSuite struct {
	FilesysSuite
}

var _ = Suite(&MemFilesysSuite{})

func (s *MemFilesysSuite) SetUpTest(c *C) {
	s.FilesysSuite = FilesysSuite{fs: filesys.NewMemFs()}
}

type DirFilesysSuite struct {
	dir string
	FilesysSuite
}

var _ = Suite(&DirFilesysSuite{})

func (s *DirFilesysSuite) SetUpTest(c *C) {
	var err error
	s.dir, err = ioutil.TempDir("", "test.dir")
	if err != nil {
		panic(err)
	}
	s.FilesysSuite = FilesysSuite{fs: filesys.NewDirFs(s.dir)}
}

func (s *DirFilesysSuite) TearDownTest(c *C) {
	err := os.RemoveAll(s.dir)
	if err != nil {
		panic(err)
	}
}
