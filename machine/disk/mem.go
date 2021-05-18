package disk

import (
	"fmt"
	"sync"
)

type MemDisk struct {
	l      *sync.RWMutex
	blocks [][BlockSize]byte
}

var _ Disk = MemDisk{}

func NewMemDisk(numBlocks uint64) MemDisk {
	blocks := make([][BlockSize]byte, numBlocks)
	return MemDisk{l: new(sync.RWMutex), blocks: blocks}
}

func (d MemDisk) ReadTo(a uint64, buf Block) {
	d.l.RLock()
	defer d.l.RUnlock()
	if a >= uint64(len(d.blocks)) {
		panic(fmt.Errorf("out-of-bounds read at %v", a))
	}
	copy(buf, d.blocks[a][:])
}

func (d MemDisk) Read(a uint64) Block {
	buf := make(Block, BlockSize)
	d.ReadTo(a, buf)
	return buf
}

func (d MemDisk) Write(a uint64, v Block) {
	if uint64(len(v)) != BlockSize {
		panic(fmt.Errorf("v is not block-sized (%d bytes)", len(v)))
	}
	d.l.Lock()
	defer d.l.Unlock()
	if a >= uint64(len(d.blocks)) {
		panic(fmt.Errorf("out-of-bounds write at %v", a))
	}
	copy(d.blocks[a][:], v)
}

func (d MemDisk) Size() uint64 {
	// this never changes so we assume it's safe to run lock-free
	return uint64(len(d.blocks))
}

func (d MemDisk) Barrier() {}

func (d MemDisk) Close() {}
