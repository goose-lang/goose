package disk

import (
	"fmt"
	"os"
	"testing"
	"time"

	"github.com/stretchr/testify/suite"
)

type DiskSuite struct {
	suite.Suite
	mem bool
	D   Disk
}

func TestMemDisk(t *testing.T) {
	suite.Run(t, &DiskSuite{mem: true})
}

func TestFileDisk(t *testing.T) {
	suite.Run(t, &DiskSuite{mem: false})
}

var diskPath = "/tmp/test-disk"

const diskSize uint64 = 100

func (suite *DiskSuite) SetupTest() {
	var d Disk
	if suite.mem {
		d = NewMemDisk(diskSize)
	} else {
		var err error
		d, err = NewFileDisk(diskPath, diskSize)
		if err != nil {
			panic(err)
		}
	}
	suite.D = d
	Init(d)
}

func (suite *DiskSuite) TearDownTest() {
	suite.D.Close()
	if !suite.mem {
		os.Remove(diskPath)
	}
}

var block0 Block = make([]byte, BlockSize)
var block1 Block = make([]byte, BlockSize)
var block2 Block = make([]byte, BlockSize)

func init() {
	block1[0] = 1
	block2[0] = 2
	diskPath += fmt.Sprintf(".%d", time.Now().UnixNano()/1000%1000)
}

func (suite *DiskSuite) TestReadWrite() {
	Write(3, block1)
	Write(4, block2)
	suite.Equal(block0, Read(2))
	suite.Equal(block1, Read(3))
	suite.Equal(block2, Read(4))
}

func (suite *DiskSuite) TestSize() {
	suite.Equal(uint64(100), Size())
}

func (suite *DiskSuite) TestBarrier() {
	Write(99, block1)
	Barrier()
	suite.Equal(block1, Read(99))
}

func (suite *DiskSuite) TestCrash() {
	if suite.mem {
		// this test doesn't make sense on an in-memory disk
		return
	}

	Write(2, block1)
	Barrier()

	suite.D.Close()
	// re-initialize to do recovery
	suite.SetupTest()

	suite.Equal(block1, Read(2))
	suite.Equal(block0, Read(3))
}

func (suite *DiskSuite) TestModifyReadBlock() {
	Write(0, block0)
	b := Read(0)
	b[0] = 1
	suite.Equal(byte(0), Read(0)[0], "Write should not retain blocks")
}

func (suite *DiskSuite) TestModifyWriteBlock() {
	b := make([]byte, 4096)
	Write(0, b)
	b[0] = 1
	suite.Equal(byte(0), Read(0)[0], "Write should not retain blocks")
}

func (suite *DiskSuite) TestReadOob() {
	suite.Panics(func() { Read(diskSize) }, "out-of-bounds read")
}

func (suite *DiskSuite) TestWriteOob() {
	suite.Panics(func() { Write(diskSize, block0) }, "out-of-bounds write")
}
