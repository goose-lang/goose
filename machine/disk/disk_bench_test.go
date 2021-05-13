package disk_test

import (
	"fmt"
	"math/rand"
	"os"
	"testing"

	"github.com/tchajed/goose/machine/disk"
)

func createMemDisk() disk.MemDisk {
	return disk.NewMemDisk(10000)
}

func createTmpDisk() (string, disk.FileDisk) {
	num := rand.Intn(1000)
	path := fmt.Sprintf("/tmp/disk-%d.img", num)

	d, err := disk.NewFileDisk(path, 10000)
	if err != nil {
		panic(err)
	}
	return path, d
}

func destroyTmpDisk(path string, d disk.FileDisk) {
	d.Close()
	os.Remove(path)
}

func benchRead10(b *testing.B, d disk.Disk) {
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
}

func BenchmarkMemRead10(b *testing.B) {
	d := createMemDisk()
	benchRead10(b, d)
}

func BenchmarkTmpFileRead10(b *testing.B) {
	path, d := createTmpDisk()
	benchRead10(b, d)
	b.StopTimer()
	destroyTmpDisk(path, d)
}

func benchWrite10(b *testing.B, d disk.Disk) {
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
}

func BenchmarkMemWrite10(b *testing.B) {
	d := createMemDisk()
	benchWrite10(b, d)
}

func BenchmarkTmpFileWrite10(b *testing.B) {
	path, d := createTmpDisk()
	benchWrite10(b, d)
	b.StopTimer()
	destroyTmpDisk(path, d)
}
