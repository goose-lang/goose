// async just uses the async disk FFI
package async

import "github.com/tchajed/goose/machine/async_disk"

func TakesDisk(d async_disk.Disk) {}

func UseDisk(d async_disk.Disk) {
	v := make([]byte, 4096)
	d.Write(0, v)
	d.Barrier()
}
