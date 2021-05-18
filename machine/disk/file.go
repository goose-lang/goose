package disk

import (
	"fmt"

	"golang.org/x/sys/unix"
)

type FileDisk struct {
	fd        int
	numBlocks uint64
}

func NewFileDisk(path string, numBlocks uint64) (FileDisk, error) {
	fd, err := unix.Open(path, unix.O_RDWR|unix.O_CREAT, 0666)
	if err != nil {
		return FileDisk{}, err
	}
	var stat unix.Stat_t
	err = unix.Fstat(fd, &stat)
	if err != nil {
		return FileDisk{}, err
	}
	if (stat.Mode&unix.S_IFREG) != 0 && uint64(stat.Size) != numBlocks {
		err = unix.Ftruncate(fd, int64(numBlocks*BlockSize))
		if err != nil {
			return FileDisk{}, err
		}
	}
	return FileDisk{fd, numBlocks}, nil
}

var _ Disk = FileDisk{}

func (d FileDisk) ReadTo(a uint64, buf Block) {
	if uint64(len(buf)) != BlockSize {
		panic("buffer is not block-sized")
	}
	if a >= d.numBlocks {
		panic(fmt.Errorf("out-of-bounds read at %v", a))
	}
	_, err := unix.Pread(d.fd, buf, int64(a*BlockSize))
	if err != nil {
		panic("read failed: " + err.Error())
	}
}

func (d FileDisk) Read(a uint64) Block {
	buf := make([]byte, BlockSize)
	d.ReadTo(a, buf)
	return buf
}

func (d FileDisk) Write(a uint64, v Block) {
	if uint64(len(v)) != BlockSize {
		panic(fmt.Errorf("v is not block sized (%d bytes)", len(v)))
	}
	if a >= d.numBlocks {
		panic(fmt.Errorf("out-of-bounds write at %v", a))
	}
	_, err := unix.Pwrite(d.fd, v, int64(a*BlockSize))
	if err != nil {
		panic("write failed: " + err.Error())
	}
}

func (d FileDisk) Size() uint64 {
	return d.numBlocks
}

func (d FileDisk) Barrier() {
	err := unix.Fsync(d.fd)
	if err != nil {
		panic("file sync failed: " + err.Error())
	}
}

func (d FileDisk) Close() {
	err := unix.Close(d.fd)
	if err != nil {
		panic(err)
	}
}
