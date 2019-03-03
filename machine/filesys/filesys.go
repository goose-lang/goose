// Package filesys is a support library providing access to a single directory
// in the filesystem.
//
// These operations have corresponding operations in Armada in `Goose/Filesys.v`
// and are exported as functions in the `FS` module.
//
// The interface is a subset of the filesystem API specific to the needs of the
// key-value store. That said, each method (with the notable exceptions of
// AtomicCreate and List) is a straightforward wrapper around a system call.
//
// AtomicCreate provides the temp file + rename pattern for convenience to
// create files atomically.
//
// List is a wrapper around readdir, which is not a system call but a library
// function that reads a directory entry in chunks and returns parsed entries
// from it. As a result the List operation is not atomic with respect to
// concurrent filesystem operations.
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
	flag.StringVar(&rootDirectory, "filesys.root", "simple.db",
		"directory to store database in")
}

// A File is a file descriptor
// (either a real OS fd or an in-memory "inode number")
type File int

func (f File) fd() int {
	return int(f)
}

// Filesys provides access a single directory.
type Filesys interface {
	// Create creates an empty file at fname (which must not exist) in
	// write-only mode
	Create(fname string) File
	// Append to an open file
	Append(f File, data []byte)
	// Close closes a file, invalidating the file descriptor
	Close(f File)
	// Open opens a file for reading
	//
	// Read-only files do not use the read offset managed by the kernel since
	// all reads are absolute.
	Open(fname string) File
	// ReadAt reads from an offset in the file (using pread)
	ReadAt(f File, offset uint64, length uint64) []byte
	// Delete deletes a file (which must exist).
	Delete(fname string)
	// AtomicCreate creates a file with data atomically using a temp file and
	// rename.
	AtomicCreate(fname string, data []byte)
	// Link creates a hard link from newName to oldName
	Link(oldName, newName string) bool
	// List lists the directory using readdir().
	//
	// This is a non-atomic operation since multiple system calls might be
	// needed to read the entire directory entry.
	List() []string
}

// Fs is a global instance of Filesys.
//
// Before using the filesystem this must be initialized (use DefaultFs, MemFs, or DirFs).
var Fs Filesys

// Re-export the filesystem methods on the global Filesys

// Create calls Create on the global Filesys
func Create(fname string) File {
	return Fs.Create(fname)
}

// Append calls Append on the global Filesys
func Append(f File, data []byte) {
	Fs.Append(f, data)
}

// Close calls Close on the global Filesys
func Close(f File) {
	Fs.Close(f)
}

// Open calls Open on the global Filesys
func Open(fname string) File {
	return Fs.Open(fname)
}

// ReadAt calls ReadAt on the global Filesys
func ReadAt(f File, offset uint64, length uint64) []byte {
	return Fs.ReadAt(f, offset, length)
}

// Delete calls Delete on the global Filesys
func Delete(fname string) {
	Fs.Delete(fname)
}

// AtomicCreate calls AtomicCreate on the global Filesys
func AtomicCreate(fname string, data []byte) {
	Fs.AtomicCreate(fname, data)
}

// Link calls Link on the global Filesys
func Link(oldName, newName string) bool {
	return Fs.Link(oldName, newName)
}

// List calls List on the global Filesys
func List() []string {
	return Fs.List()
}

// DefaultFs returns a directory filesystem using the global flag configuration.
func DefaultFs() Filesys {
	if !flag.Parsed() {
		panic("default filesystem relies on flag parsing")
	}
	return NewDirFs(rootDirectory)
}

// DirFs is a Filesys backed by a directory on some host filesystem.
type DirFs struct {
	rootDirectory string
}

// NewDirFs creates a DirFs using root as the root directory for all operations.
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
