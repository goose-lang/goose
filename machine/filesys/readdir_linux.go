package filesys

import "syscall"

func readDirents(fd int, buf []byte) (n int, err error) {
	return syscall.Getdents(fd, buf)
}
