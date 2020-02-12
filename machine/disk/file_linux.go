package disk

import (
	"golang.org/x/sys/unix"
)

func openNormal(path string, mode int, perm uint32) (fd int, err error) {
	return unix.Open(path, mode, perm)
}

func openDirect(path string, mode int, perm uint32) (fd int, err error) {
	return unix.Open(path, mode|unix.O_DIRECT, perm)
}
