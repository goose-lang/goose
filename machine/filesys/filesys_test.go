package filesys_test

import (
	"fmt"
	"io/ioutil"
	"os"
	"sort"
	"testing"

	"github.com/stretchr/testify/suite"
	"github.com/tchajed/goose/machine/filesys"
)

// FilesysSuite implements a filesystem test suite generic over fs.
type FilesysSuite struct {
	suite.Suite
	dir string
	fs  filesys.Filesys
}

func (s *FilesysSuite) SetupTest() {
	if s.dir == ":memory:" {
		s.fs = filesys.NewMemFs()
	} else {
		var err error
		s.dir, err = ioutil.TempDir("", "test.dir")
		if err != nil {
			panic(err)
		}
		s.fs = filesys.NewDirFs(s.dir)
	}
	s.setupDirs()
}

func (s *FilesysSuite) TearDownTest() {
	if s.dir != ":memory:" {
		s.fs.(filesys.DirFs).CloseFs()
		err := os.RemoveAll(s.dir)
		if err != nil {
			panic(err)
		}
	}
}

func (s *FilesysSuite) setupDirs() {
	s.fs.Mkdir("dir")
	s.fs.Mkdir("dir1")
	s.fs.Mkdir("dir2")
}

func (s *FilesysSuite) CreateNew(fname string) filesys.File {
	f, ok := s.fs.Create("dir", fname)
	if !ok {
		panic(fmt.Errorf("destination file %s/%s exists", "dir", fname))
	}
	return f
}

func (s *FilesysSuite) TestCreateReadExact() {
	written := []byte("some data")
	f := s.CreateNew("test.bin")
	s.fs.Append(f, written)
	s.fs.Close(f)

	f2 := s.fs.Open("dir", "test.bin")
	data := s.fs.ReadAt(f2, 0, uint64(len(written)))
	s.Equal(written, data)
}

// readAllIn only works for files < 4096 bytes
func (s *FilesysSuite) readAllIn(dir, fname string) []byte {
	f := s.fs.Open(dir, fname)
	data := s.fs.ReadAt(f, 0, 4096)
	s.fs.Close(f)
	return data
}

// readAllIn only works for files < 4096 bytes
func (s *FilesysSuite) readAll(fname string) []byte {
	return s.readAllIn("dir", fname)
}

func (s *FilesysSuite) TestCreateReadExtra() {
	written := []byte("some data")
	f := s.CreateNew("test.bin")
	s.fs.Append(f, written)
	s.fs.Close(f)

	data := s.readAll("test.bin")
	s.Equal(written, data)
}

func (s *FilesysSuite) TestReadAtOob() {
	f := s.CreateNew("test.bin")
	s.fs.Append(f, []byte("some data"))
	s.fs.Close(f)

	f2 := s.fs.Open("dir", "test.bin")
	data := s.fs.ReadAt(f2, 1000, 10)
	s.Empty(data)
}

func (s *FilesysSuite) TestReadAtOffset() {
	written := []byte("some longer data")
	f := s.CreateNew("test.bin")
	s.fs.Append(f, written)
	s.fs.Close(f)

	f2 := s.fs.Open("dir", "test.bin")
	data := s.fs.ReadAt(f2, uint64(len("some ")), uint64(len("longer")))
	s.Equal([]byte("longer"), data)
}

// for checking directory listings in canonical order
func sorted(s []string) []string {
	sort.Slice(s, func(i, j int) bool {
		return s[i] < s[j]
	})
	return s
}

func (s *FilesysSuite) TestList() {
	s.Empty(s.fs.List("dir"))
	s.fs.Close(s.CreateNew("f1"))
	s.fs.Close(s.CreateNew("f2"))
	s.Equal([]string{"f1", "f2"}, sorted(s.fs.List("dir")))
}

func (s *FilesysSuite) TestListLargeDir() {
	s.Empty(s.fs.List("dir"))
	var expected []string
	for i := 0; i < 1000; i++ {
		fname := fmt.Sprintf("file%d", i)
		s.fs.Close(s.CreateNew(fname))
		expected = append(expected, fname)
	}
	s.Equal(sorted(expected), sorted(s.fs.List("dir")))
}

func (s *FilesysSuite) TestDelete() {
	s.fs.Close(s.CreateNew("f1"))
	s.fs.Close(s.CreateNew("f2"))
	s.Equal([]string{"f1", "f2"}, sorted(s.fs.List("dir")))
	s.fs.Delete("dir", "f1")
	s.Equal([]string{"f2"}, sorted(s.fs.List("dir")))
}

func (s *FilesysSuite) TestAtomicCreate() {
	contents := []byte("hello world")
	s.fs.AtomicCreate("dir", "testfile", contents)
	f := s.fs.Open("dir", "testfile")
	data := s.fs.ReadAt(f, 0, uint64(len(contents)))
	s.Equal(contents, data)
}

func (s *FilesysSuite) TestLink() {
	contents := []byte("hello world")
	s.fs.AtomicCreate("dir", "file1", contents)
	ok := s.fs.Link("dir", "file1", "dir", "file2")
	s.Assert().Equal(true, ok)
	ok = s.fs.Link("dir", "file2", "dir", "file1")
	s.Equal(false, ok)
	s.Equal(contents, s.readAll("file1"))
	s.Equal(contents, s.readAll("file2"))
	s.fs.Delete("dir", "file1")
	s.Equal(contents, s.readAll("file2"))
	s.Equal([]string{"file2"}, sorted(s.fs.List("dir")))
}

func (s *FilesysSuite) TestReadIndependentDirs() {
	written1 := []byte("some data")
	f, _ := s.fs.Create("dir1", "test.bin")
	s.fs.Append(f, written1)
	s.fs.Close(f)

	written2 := []byte("other data")
	f, _ = s.fs.Create("dir2", "test.bin")
	s.fs.Append(f, written2)
	s.fs.Close(f)

	data1 := s.readAllIn("dir1", "test.bin")
	s.Equal(written1, data1)
	data2 := s.readAllIn("dir2", "test.bin")
	s.Equal(written2, data2)
}

func TestMemFilesys(t *testing.T) {
	suite.Run(t, &FilesysSuite{dir: ":memory:"})
}

func TestDirFilesys(t *testing.T) {
	suite.Run(t, &FilesysSuite{})
}
