package unittest

import "github.com/tchajed/goose/machine/disk"

type diskWrapper struct {
	d disk.Disk
}

func diskArgument(d disk.Disk) {
	b := d.Read(0)
	d.Write(1, b)
}
