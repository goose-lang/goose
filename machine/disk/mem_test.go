package disk_test

import (
	"testing"

	"github.com/tchajed/goose/machine/disk"
)

func BenchmarkMemRead10(b *testing.B) {
	d := disk.NewMemDisk(100)
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := uint64(0); j < 10; j++ {
			d.Read(j)
		}
	}
}

func BenchmarkMemWrite10(b *testing.B) {
	d := disk.NewMemDisk(100)
	data := make([]byte, 4096)
	copy(data, []byte{1, 2, 3, 4})
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := uint64(0); j < 10; j++ {
			d.Write(j, data)
		}
	}
}
