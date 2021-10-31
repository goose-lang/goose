package async_disk

import (
	"github.com/tchajed/goose/machine/disk"
)

// Essentially a copy + paste of the disk interface. We do this so that we can
// change what Goose translate client code to (either the Disk FFI model or
// Async Disk FFI model) based on which package is used.

// Block is a 4096-byte buffer
type Block = disk.Block
const BlockSize uint64 = disk.BlockSize
type Disk = disk.Disk

/*
// Disk provides access to a logical block-based disk
type Disk interface {
	// Read reads a disk block by address
	//
	// Expects a < Size().
	Read(a uint64) Block

	// ReadTo reads the disk block at a and stores the result in b
	//
	// Expects a < Size().
	ReadTo(a uint64, b Block)

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

var implicitDisk Disk

// Init sets up the global disk
func Init(d Disk) {
	implicitDisk = d
}

// Get returns the previously-initialized global disk
func Get() Disk {
	return implicitDisk
}

// Read (see the Disk documentation)
//
// Deprecated: use Get() and the Disk method
func Read(a uint64) Block {
	return implicitDisk.Read(a)
}

// Write (see the Disk documentation)
//
// Deprecated: use Get() and the Disk method
func Write(a uint64, v Block) {
	implicitDisk.Write(a, v)
}

// Size (see the Disk documentation)
//
// Deprecated: use Get() and the Disk method
func Size() uint64 {
	return implicitDisk.Size()
}

// Barrier (see the Disk documentation)
//
// Deprecated: use Get() and the Disk method
func Barrier() {
	implicitDisk.Barrier()
}
*/
