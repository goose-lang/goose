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
