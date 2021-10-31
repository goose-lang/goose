package async_disk

import (
	"github.com/tchajed/goose/machine/disk"
)

type FileDisk = disk.FileDisk

func NewFileDisk(path string, numBlocks uint64) (FileDisk, error) {
	return disk.NewFileDisk(path, numBlocks)
}

var _ Disk = FileDisk{}
