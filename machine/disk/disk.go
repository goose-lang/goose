package disk

import "fmt"

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
}

type MemDisk []Block

var _ Disk = MemDisk(nil)

func NewMemDisk(numBlocks uint64) MemDisk {
	disk := make([]Block, numBlocks)
	for i := range disk {
		disk[i] = make([]byte, BlockSize)
	}
	return disk
}

func (d MemDisk) Read(a uint64) Block {
	return d[a]
}

func (d MemDisk) Write(a uint64, v Block) {
	if uint64(len(v)) != BlockSize {
		panic(fmt.Errorf("v is not block-sized (%d bytes)", len(v)))
	}
	d[a] = v
}

func (d MemDisk) Size() uint64 {
	return uint64(len(d))
}

func (d MemDisk) Barrier() {}

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
