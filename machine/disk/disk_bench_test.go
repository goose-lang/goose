package disk_test

import (
	"flag"
	"fmt"
	"math/rand"
	"os"
	"testing"

	"github.com/goose-lang/goose/machine/disk"
)

var diskFile = flag.String("disk", "", "path to file to use for disk-based benchmark")

func createMemDisk() disk.MemDisk {
	return disk.NewMemDisk(10000)
}

func createTmpPath() string {
	num := rand.Intn(1000)
	return fmt.Sprintf("/tmp/disk-%d.img", num)
}

func createFileDisk(path string) disk.FileDisk {
	d, err := disk.NewFileDisk(path, 10000)
	if err != nil {
		panic(err)
	}
	return d
}

func destroyFileDisk(path string, d disk.FileDisk) {
	d.Close()
	f, err := os.Stat(path)
	if err != nil {
		panic(err)
	}
	if f.Mode().IsRegular() {
		os.Remove(path)
	}
}

// Run benchmark f on several disks, as sub-benchmarks
func benchmarkOnDisks(b *testing.B, f func(b *testing.B, d disk.Disk)) {
	b.Helper()
	b.Run("Mem", func(b *testing.B) {
		d := createMemDisk()
		f(b, d)
	})
	b.Run("TmpFile", func(b *testing.B) {
		path := createTmpPath()
		d := createFileDisk(path)
		defer destroyFileDisk(path, d)
		f(b, d)
		b.StopTimer()
	})
	if *diskFile != "" {
		b.Run("DiskFile", func(b *testing.B) {
			path := *diskFile
			d := createFileDisk(path)
			defer destroyFileDisk(path, d)
			f(b, d)
			b.StopTimer()
		})
	}
}

func BenchmarkRead10(b *testing.B) {
	benchmarkOnDisks(b,
		func(b *testing.B, d disk.Disk) {
			size := d.Size()
			b.ResetTimer()
			iter := uint64(0)
			for i := 0; i < b.N; i++ {
				for j := uint64(0); j < 10; j++ {
					d.Read(iter % size)
					iter++
				}
			}
			b.ReportMetric(float64(iter)*4/1024, "MB/s")
		})
}

func BenchmarkWrite10(b *testing.B) {
	benchmarkOnDisks(b, func(b *testing.B, d disk.Disk) {
		size := d.Size()
		data := make([]byte, 4096)
		copy(data, []byte{1, 2, 3, 4})
		b.ResetTimer()
		iter := uint64(0)
		for i := 0; i < b.N; i++ {
			for j := uint64(0); j < 10; j++ {
				d.Write(iter%size, data)
				iter++
			}
		}
		b.ReportMetric(float64(iter)*4/1024, "MB/s")
	})
}

func BenchmarkBarrierOneWrite(b *testing.B) {
	benchmarkOnDisks(b, func(b *testing.B, d disk.Disk) {
		size := d.Size()
		data := make([]byte, 4096)
		copy(data, []byte{1, 2, 3, 4})
		b.ResetTimer()
		iter := uint64(0)
		for i := 0; i < b.N; i++ {
			d.Write(iter%size, data)
			d.Barrier()
			iter++
		}
	})
}

func BenchmarkBarrierWrite10(b *testing.B) {
	benchmarkOnDisks(b, func(b *testing.B, d disk.Disk) {
		size := d.Size()
		data := make([]byte, 4096)
		copy(data, []byte{1, 2, 3, 4})
		b.ResetTimer()
		iter := uint64(0)
		for i := 0; i < b.N; i++ {
			for j := 0; j < 10; j++ {
				d.Write(iter%size, data)
			}
			d.Barrier()
			iter++
		}
	})
}
