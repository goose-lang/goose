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

func BenchmarkSequentialWrite(b *testing.B) {
	zero := make([]byte, 4096)
	d := disk.NewMemDisk(uint64(b.N))
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		d.Write(uint64(i), zero)
	}
	b.ReportMetric(float64(b.N)*4/1024, "MB/s")
}

func BenchmarkSequentialRead(b *testing.B) {
	size := 10000
	d := disk.NewMemDisk(10000)
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		d.Read(uint64(i % size))
	}
	b.ReportMetric(float64(b.N)*4/1024, "MB/s")
}
