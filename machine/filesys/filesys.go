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

// Filesys provides access a directory with one layer of nested directories.
type Filesys interface {
	// Create creates an empty file at fname in write-only mode.
	// Returns ok=false and does nothing if fname exists.
	Create(dir, fname string) (f File, ok bool)
	// Append to an open file
	Append(f File, data []byte)
	// Close closes a file, invalidating the file descriptor
	Close(f File)
	// Open opens a file for reading
	//
	// Read-only files do not use the read offset managed by the kernel since
	// all reads are absolute.
	Open(dir, fname string) File
	// ReadAt reads from an offset in the file (using pread)
	ReadAt(f File, offset uint64, length uint64) []byte
	// Delete deletes a file (which must exist).
	Delete(dir, fname string)
	// AtomicCreate creates a file with data atomically using a temp file and
	// rename.
	AtomicCreate(dir, fname string, data []byte)
	// Link creates a hard link from newName to oldName
	Link(oldDir, oldName, newDir, newName string) bool
	// List lists the directory using readdir().
	//
	// This is a non-atomic operation since multiple system calls might be
	// needed to read the entire directory entry.
	List(dir string) []string
	// Mkdir creates a root directory.
	//
	// Used only for initialization outside of verified code
	// (Armada's Go model does not model this operation).
	Mkdir(dir string)
}

// Fs is a global instance of Filesys.
//
// Before using the filesystem this must be initialized (use DefaultFs, MemFs, or DirFs).
var Fs Filesys

// Re-export the filesystem methods on the global Filesys

// Create calls Create on the global Filesys
func Create(dir, fname string) (File, bool) {
	return Fs.Create(dir, fname)
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
func Open(dir, fname string) File {
	return Fs.Open(dir, fname)
}

// ReadAt calls ReadAt on the global Filesys
func ReadAt(f File, offset uint64, length uint64) []byte {
	return Fs.ReadAt(f, offset, length)
}

// Delete calls Delete on the global Filesys
func Delete(dir, fname string) {
	Fs.Delete(dir, fname)
}

// AtomicCreate calls AtomicCreate on the global Filesys
func AtomicCreate(dir, fname string, data []byte) {
	Fs.AtomicCreate(dir, fname, data)
}

// Link calls Link on the global Filesys
func Link(oldDir, oldName, newDir, newName string) bool {
	return Fs.Link(oldDir, oldName, newDir, newName)
}

// List calls List on the global Filesys
func List(dir string) []string {
	return Fs.List(dir)
}

// DefaultFs returns a directory filesystem using the global flag configuration.
func DefaultFs() Filesys {
	if !flag.Parsed() {
		panic("default filesystem relies on flag parsing")
	}
	return NewDirFs(rootDirectory)
}
