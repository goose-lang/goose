package filesys

import (
	"path"

	"golang.org/x/sys/unix"
)

func (fs DirFs) AtomicCreate(dir, fname string, data []byte) {
	tmpFile := fname + ".tmp"
	fd, err := unix.Openat(fs.rootFd, tmpFile,
		unix.O_CREAT|unix.O_WRONLY, 0644)
	if err != nil {
		panic(err)
	}
	defer unix.Close(fd)
	for len(data) > 0 {
		n, err := unix.Write(fd, data)
		if err != nil {
			panic(err)
		}
		data = data[n:]
	}
	err = unix.Fsync(fd)
	if err != nil {
		panic(err)
	}
	err = unix.Renameat(fs.rootFd, tmpFile, fs.rootFd, path.Join(dir, fname))
	if err != nil {
		panic(err)
	}
}
