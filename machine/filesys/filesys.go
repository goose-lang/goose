package filesys

import (
	"flag"
	"fmt"
	"io"

	"github.com/spf13/afero"
)

var rootDirectory string

func init() {
	flag.StringVar(&rootDirectory, "filesys.root", "simple.db", "directory to store database in")
}

// File is an opaque handle to a file. Unlike typical Go, File does not have
// methods and instead must be passed back to a filesystem to anything with it.
type File afero.File

// Filesys provides access a single directory.
type Filesys interface {
	Create(fname string) File
	Append(f File, data []byte)
	Close(f File)
	Open(fname string) File
	ReadAt(f File, offset uint64, length uint64) []byte
}

// Fs is a global instance of Filesys.
//
// Before using the filesystem this must be initialized (use DefaultFs, MemFs, or DirFs).
var Fs Filesys

// Re-export the filesystem methods on the global Filesys

func Create(fname string) File {
	return Fs.Create(fname)
}

func Append(f File, data []byte) {
	Fs.Append(f, data)
}

func Close(f File) {
	Fs.Close(f)
}

func Open(fname string) File {
	return Fs.Open(fname)
}

func ReadAt(f File, offset uint64, length uint64) []byte {
	return Fs.ReadAt(f, offset, length)
}

type filesys struct {
	fs afero.Afero
}

// Init prepares the global filesystem Fs to a single directory based on flags.
func DefaultFs() Filesys {
	if !flag.Parsed() {
		panic("default filesystem relies on flag parsing")
	}
	return DirFs(rootDirectory)
}

func fromAfero(fs afero.Fs) filesys {
	return filesys{afero.Afero{Fs: fs}}
}

// MemFs creates an in-memory Filesys
func MemFs() Filesys {
	fs := afero.NewMemMapFs()
	return fromAfero(fs)
}

// DirFs creates a Filesys backed by the OS, using basedir.
//
// Creates basedir if it does not exist.
func DirFs(basedir string) Filesys {
	fs := afero.NewOsFs()
	ok, err := afero.Exists(fs, basedir)
	if err != nil {
		panic(err)
	}
	if !ok {
		err = fs.Mkdir(basedir, 0755)
		if err != nil {
			panic(err)
		}
	}
	baseFs := afero.NewBasePathFs(fs, basedir)
	return fromAfero(baseFs)
}

func abs(fname string) string {
	return fmt.Sprintf("/%s", fname)
}

// Create an appendable file
func (fs filesys) Create(fname string) File {
	f, err := fs.fs.Create(abs(fname))
	if err != nil {
		panic(err)
	}
	return File(f)
}

// Append to a file
func (fs filesys) Append(f File, data []byte) {
	_, err := f.Write(data)
	if err != nil {
		panic(err)
	}
}

// Close a file
//
// Frees up file descriptor. Further operations are illegal.
func (fs filesys) Close(f File) {
	err := f.Close()
	if err != nil {
		panic(err)
	}
}

// Open a file in read-only mode.
func (fs filesys) Open(fname string) File {
	f, err := fs.fs.Open(abs(fname))
	if err != nil {
		panic(err)
	}
	return File(f)
}

// ReadAt reads data from an absolute position in the file.
//
// Readable files never modify or use the file descriptor seek pointer.
func (fs filesys) ReadAt(f File, offset uint64, length uint64) []byte {
	p := make([]byte, length)
	n, err := f.ReadAt(p, int64(offset))
	// we use ReadAt slightly differently than Go expects, and EOF during a ReadAt is expected
	if err != nil && err != io.EOF {
		panic(err)
	}
	return p[:n]
}
