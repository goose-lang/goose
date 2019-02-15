package filesys

import (
	"os"
	"path"
	"testing"
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
	fs Filesys
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

type MemFilesysSuite struct {
	FilesysSuite
}

var _ = Suite(&MemFilesysSuite{})

func (s *MemFilesysSuite) SetUpTest(c *C) {
	s.FilesysSuite = FilesysSuite{fs: MemFs()}
}

type DirFilesysSuite struct {
	dir string
	FilesysSuite
}

var _ = Suite(&DirFilesysSuite{})

func (s *DirFilesysSuite) SetUpTest(c *C) {
	s.dir = path.Join(os.TempDir(), "test.dir")
	err := os.Mkdir(s.dir, 0744)
	if err != nil {
		panic(err)
	}
	s.FilesysSuite = FilesysSuite{fs: DirFs(s.dir)}
}

func (s *DirFilesysSuite) TearDownTest(c *C) {
	err := os.RemoveAll(s.dir)
	if err != nil {
		panic(err)
	}
}
