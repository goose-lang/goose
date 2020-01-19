package disk

import (
	"fmt"
	"sync"
)

// Block is a 4096-byte buffer
type Block = []byte

const BlockSize uint64 = 4096

// Disk provides access to a logical block-based disk
type Disk interface {
	// Read reads a disk block by address
	//
	// Expects a < Size().
	Read(a uint64) Block

	// Write updates a disk block by address
	//
	// Expects a < Size().
	Write(a uint64, v Block)

	// Size reports how big the disk is, in blocks
	Size() uint64

	// Barrier ensures data is persisted.
	//
	// When it returns, all outstanding writes are guaranteed to be durably on
	// disk
	Barrier()

	// Close releases any resources used by the disk and makes it unusable.
	Close()
}

type MemDisk struct {
	l      *sync.RWMutex
	blocks []Block
}

var _ Disk = MemDisk{}

func NewMemDisk(numBlocks uint64) MemDisk {
	blocks := make([]Block, numBlocks)
	for i := range blocks {
		blocks[i] = make([]byte, BlockSize)
	}
	return MemDisk{l: new(sync.RWMutex), blocks: blocks}
}

func (d MemDisk) Read(a uint64) Block {
	d.l.RLock()
	defer d.l.RUnlock()
	blk := make([]byte, BlockSize)
	copy(blk, d.blocks[a])
	return blk
}

func (d MemDisk) Write(a uint64, v Block) {
	if uint64(len(v)) != BlockSize {
		panic(fmt.Errorf("v is not block-sized (%d bytes)", len(v)))
	}
	d.l.Lock()
	defer d.l.Unlock()
	blk := make([]byte, BlockSize)
	copy(blk, v)
	d.blocks[a] = blk
}

func (d MemDisk) Size() uint64 {
	// this never changes so we assume it's safe to run lock-free
	return uint64(len(d.blocks))
}

func (d MemDisk) Barrier() {}

func (d MemDisk) Close() {}

var implicitDisk Disk

// Init sets up the global disk
func Init(d Disk) {
	implicitDisk = d
}

// Read (see the Disk documentation)
func Read(a uint64) Block {
	return implicitDisk.Read(a)
}

// Write (see the Disk documentation)
func Write(a uint64, v Block) {
	implicitDisk.Write(a, v)
}

// Size (see the Disk documentation)
func Size() uint64 {
	return implicitDisk.Size()
}

// Barrier (see the Disk documentation)
func Barrier() {
	implicitDisk.Barrier()
}
