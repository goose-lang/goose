package disk

import (
	"fmt"
	"os"
)

type FileDisk struct {
	f         *os.File
	numBlocks uint64
}

var _ Disk = FileDisk{}

func NewFileDisk(path string, numBlocks uint64) (FileDisk, error) {
	f, err := os.Create(path)
	if err != nil {
		return FileDisk{}, err
	}
	err = f.Truncate(int64(numBlocks * BlockSize))
	if err != nil {
		return FileDisk{}, err
	}
	return FileDisk{f, numBlocks}, nil
}

func OpenFileDisk(path string) (FileDisk, error) {
	f, err := os.Open(path)
	if err != nil {
		return FileDisk{}, err
	}
	finfo, err := f.Stat()
	if err != nil {
		return FileDisk{}, err
	}
	numBlocks := uint64(finfo.Size()) / BlockSize
	return FileDisk{f, numBlocks}, nil
}

func (d FileDisk) Read(a uint64) Block {
	buf := make([]byte, BlockSize)
	if a >= d.numBlocks {
		panic("out-of-bounds read")
	}
	_, err := d.f.ReadAt(buf, int64(a*BlockSize))
	if err != nil {
		panic("read failed: " + err.Error())
	}
	return buf
}

func (d FileDisk) Write(a uint64, v Block) {
	if uint64(len(v)) != BlockSize {
		panic(fmt.Errorf("v is not block sized (%d bytes)", len(v)))
	}
	if a > d.numBlocks {
		panic("out-of-bounds read")
	}
	_, err := d.f.WriteAt(v, int64(a*BlockSize))
	if err != nil {
		panic("write failed: " + err.Error())
	}
}

func (d FileDisk) Size() uint64 {
	return d.numBlocks
}

func (d FileDisk) Barrier() {
	err := d.f.Sync()
	if err != nil {
		panic("file sync failed: " + err.Error())
	}
}

func (d FileDisk) Close() {
	err := d.f.Close()
	if err != nil {
		panic(err)
	}
}
