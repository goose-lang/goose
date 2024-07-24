package async_disk

import (
	"github.com/goose-lang/goose/machine/disk"
)

type MemDisk = disk.MemDisk

func NewMemDisk(numBlocks uint64) MemDisk {
	return MemDisk(disk.NewMemDisk(numBlocks))
}

var _ Disk = MemDisk{}
