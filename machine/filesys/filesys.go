package filesys

import (
	"flag"
	"fmt"
	"os"
	"path"
	"syscall"
)

var rootDirectory string

func init() {
	flag.StringVar(&rootDirectory, "filesys.root", "simple.db", "directory to store database in")
}

// A File is a file descriptor
// (either a real OS fd or an in-memory "inode number")
type File int

func (f File) fd() int {
	return int(f)
}

// Filesys provides access a single directory.
type Filesys interface {
	Create(fname string) File
	Append(f File, data []byte)
	Close(f File)
	Open(fname string) File
	ReadAt(f File, offset uint64, length uint64) []byte
	Delete(fname string)
	AtomicCreate(fname string, data []byte)
	Link(oldName, newName string) bool
	List() []string
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

func Delete(fname string) {
	Fs.Delete(fname)
}

func AtomicCreate(fname string, data []byte) {
	Fs.AtomicCreate(fname, data)
}

func Link(oldName, newName string) bool {
	return Fs.Link(oldName, newName)
}

func List() []string {
	return Fs.List()
}

// Init prepares the global filesystem Fs to a single directory based on flags.
func DefaultFs() Filesys {
	if !flag.Parsed() {
		panic("default filesystem relies on flag parsing")
	}
	return NewDirFs(rootDirectory)
}

type DirFs struct {
	rootDirectory string
}

func NewDirFs(root string) DirFs {
	return DirFs{rootDirectory: root}
}

func (fs DirFs) resolve(p string) string {
	return path.Join(fs.rootDirectory, p)
}

func (fs DirFs) Create(fname string) File {
	fd, err := syscall.Open(fs.resolve(fname),
		syscall.O_CREAT|syscall.O_WRONLY, 0644)
	if err != nil {
		panic(err)
	}
	return File(fd)
}

func (fs DirFs) Append(f File, data []byte) {
	n, err := syscall.Write(f.fd(), data)
	if err != nil {
		panic(err)
	}
	if n < len(data) {
		panic(fmt.Errorf("short write: %d < %d bytes", n, len(data)))
	}
}

func (fs DirFs) Close(f File) {
	err := syscall.Close(f.fd())
	if err != nil {
		panic(err)
	}
}

func (fs DirFs) Open(fname string) File {
	fd, err := syscall.Open(fs.resolve(fname),
		syscall.O_RDONLY, 0)
	if err != nil {
		panic(err)
	}
	return File(fd)
}

func (fs DirFs) ReadAt(f File, offset uint64, length uint64) []byte {
	p := make([]byte, length)
	n, err := syscall.Pread(f.fd(), p, int64(offset))
	if err != nil {
		panic(err)
	}
	return p[:n]
}

func (fs DirFs) Delete(fname string) {
	err := syscall.Unlink(fs.resolve(fname))
	if err != nil {
		panic(fmt.Errorf("unlink(%s): %s", fname, err))
	}
}

func (fs DirFs) AtomicCreate(fname string, data []byte) {
	tmpFile := fs.resolve(fname + ".tmp")
	fd, err := syscall.Open(tmpFile,
		syscall.O_CREAT|syscall.O_WRONLY, 0644)
	if err != nil {
		panic(err)
	}
	for len(data) > 0 {
		n, err := syscall.Write(fd, data)
		if err != nil {
			panic(err)
		}
		data = data[n:]
	}
	err = syscall.Rename(tmpFile, fs.resolve(fname))
	if err != nil {
		panic(err)
	}
}

func (fs DirFs) Link(oldName, newName string) bool {
	err := syscall.Link(fs.resolve(oldName), fs.resolve(newName))
	if err != nil {
		return false
	}
	return true
}

func (fs DirFs) List() []string {
	d, err := os.Open(fs.rootDirectory)
	if err != nil {
		panic(err)
	}
	names, err := d.Readdirnames(0)
	if err != nil {
		panic(err)
	}
	return names
}
