package async_disk

import (
	"github.com/tchajed/goose/machine/disk"
)

type MemDisk = disk.MemDisk

func NewMemDisk(numBlocks uint64) MemDisk {
	return MemDisk(disk.NewMemDisk(numBlocks))
}

var _ Disk = MemDisk{}

/* 
func (d MemDisk) ReadTo(a uint64, buf Block) {
	d.disk.ReadTo(a, buf)
}

func (d MemDisk) Read(a uint64) Block {
	return d.disk.Read(a)
}

func (d MemDisk) Write(a uint64, v Block) {
	d.disk.Write(a, v)
}

func (d MemDisk) Size() uint64 {
	return d.disk.Size()
}

func (d MemDisk) Barrier() { d.disk.Barrier() }

func (d MemDisk) Close() { d.disk.Close () }
*/
