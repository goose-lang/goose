package disk

import "golang.org/x/sys/unix"

func openNormal(path string, mode int, perm uint32) (fd int, err error) {
	return unix.Open(path, mode, perm)
}

func openDirect(path string, mode int, perm uint32) (fd int, err error) {
	fd, err = unix.Open(path, mode, perm)
	if err != nil {
		return
	}
	_, err = unix.FcntlInt(uintptr(fd), unix.F_NOCACHE, 1)
	if err != nil {
		panic(err)
	}
	return
}
