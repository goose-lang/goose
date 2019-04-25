package filesys

import (
	"fmt"
	"path"

	"github.com/pkg/errors"
	"golang.org/x/sys/unix"
)

// DirFs is a Filesys backed by a directory on some host filesystem.
type DirFs struct {
	rootFd int
}

// NewDirFs creates a DirFs using root as the root directory for all operations.
func NewDirFs(root string) DirFs {
	rootFd, err := unix.Open(root, unix.O_DIRECTORY|unix.O_RDONLY, 0)
	if err != nil {
		panic(err)
	}
	return DirFs{rootFd: rootFd}
}

func (fs DirFs) Mkdir(p string) {
	err := unix.Mkdirat(fs.rootFd, p, 0755)
	if err != nil {
		panic(err)
	}
}

func (fs DirFs) Create(dir, fname string) (f File, ok bool) {
	fd, err := unix.Openat(fs.rootFd, path.Join(dir, fname),
		unix.O_CREAT|unix.O_EXCL|unix.O_WRONLY, 0644)
	if err == unix.EEXIST {
		return File(-1), false
	}
	if err != nil {
		panic(err)
	}
	return File(fd), true
}

func (fs DirFs) Append(f File, data []byte) {
	n, err := unix.Write(f.fd(), data)
	if err != nil {
		panic(err)
	}
	if n < len(data) {
		panic(fmt.Errorf("short write: %d < %d bytes", n, len(data)))
	}
}

func (fs DirFs) Close(f File) {
	err := unix.Close(f.fd())
	if err != nil {
		panic(err)
	}
}

func (fs DirFs) Open(dir, fname string) File {
	fd, err := unix.Openat(fs.rootFd, path.Join(dir, fname),
		unix.O_RDONLY, 0)
	if err != nil {
		panic(err)
	}
	return File(fd)
}

func (fs DirFs) ReadAt(f File, offset uint64, length uint64) []byte {
	p := make([]byte, length)
	n, err := unix.Pread(f.fd(), p, int64(offset))
	if err != nil {
		panic(err)
	}
	return p[:n]
}

func (fs DirFs) Delete(dir, fname string) {
	err := unix.Unlinkat(fs.rootFd, path.Join(dir, fname), 0)
	if err != nil {
		panic(fmt.Errorf("unlink(%s): %s", fname, err))
	}
}

func (fs DirFs) Link(oldDir, oldName, newDir, newName string) bool {
	err := unix.Linkat(fs.rootFd, path.Join(oldDir, oldName),
		fs.rootFd, path.Join(newDir, newName),
		0)
	return err == nil
}

func (fs DirFs) List(dir string) []string {
	d, err := unix.Openat(fs.rootFd, dir, unix.O_DIRECTORY, 0)
	if err != nil {
		panic(err)
	}
	defer unix.Close(d)
	// written to match dir_unix.go's (f *os.File) readdirnames()
	// as much as possible, except to always read all the entries
	// in the directory without an n limit
	bufp := 0
	nbuf := 0
	buf := make([]byte, 4096)
	names := make([]string, 0, 100)
	for {
		// Refill the buffer if necessary
		if bufp >= nbuf {
			bufp = 0
			var errno error
			nbuf, errno = unix.ReadDirent(d, buf)
			if errno != nil {
				panic(errors.Wrapf(errno, "readdirent %s", dir))
			}
			if nbuf <= 0 {
				break // EOF
			}
		}

		// Drain the buffer by parsing entries
		var nb int
		nb, _, names = unix.ParseDirent(buf[bufp:nbuf], 100, names)
		bufp += nb
	}
	return names
}
