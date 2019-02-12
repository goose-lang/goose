package filesys

import (
	"flag"
	"fmt"

	"github.com/spf13/afero"
)

var rootDirectory string

func init() {
	flag.StringVar(&rootDirectory, "root", "simple.db", "directory to store database in")
}

// File is an opaque handle to a file. Unlike typical Go, File does not have
// methods and instead must be passed back to a filesystem to anything with it.
type File afero.File

// Filesys wraps access to the single-directory filesystem API.
type Filesys struct {
	fs afero.Afero
}

// Fs is a global instance of filesystem.
//
// Configure with flags (calling flags.Parse()), then initialize with Init.
var Fs Filesys

// Init prepares the global filesystem Fs
func Init() {
	Fs = DirFs(rootDirectory)
}

func fromAfero(fs afero.Fs) Filesys {
	return Filesys{afero.Afero{Fs: fs}}
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
func (fs Filesys) Create(fname string) File {
	f, err := fs.fs.Create(abs(fname))
	if err != nil {
		panic(err)
	}
	return File(f)
}

// Append to a file
func (fs Filesys) Append(f File, data []byte) {
	_, err := f.Write(data)
	if err != nil {
		panic(err)
	}
}

// Close a file
//
// Frees up file descriptor. Further operations are illegal.
func (fs Filesys) Close(f File) {
	err := f.Close()
	if err != nil {
		panic(err)
	}
}

// Open a file in read-only mode.
func (fs Filesys) Open(fname string) File {
	f, err := fs.fs.Open(abs(fname))
	if err != nil {
		panic(err)
	}
	return File(f)
}

// ReadAt reads data from an absolute position in the file.
//
// Readable files never modify or use the file descriptor seek pointer.
func (fs Filesys) ReadAt(f File, offset uint64, length uint64) []byte {
	p := make([]byte, length)
	n, err := f.ReadAt(p, int64(offset))
	if n != len(p) {
		panic(fmt.Errorf("short ReadAt(%d, %d) -> %d bytes for %s", offset, length, n, f.Name()))
	}
	if err != nil {
		panic(err)
	}
	return p
}
