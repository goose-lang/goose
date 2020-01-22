package disk

import (
	"fmt"
	"os"
	"testing"
	"time"

	. "gopkg.in/check.v1"
)

func Test(t *testing.T) { TestingT(t) }

type DiskSuite struct {
	mem bool
	D   Disk
}

var _ = Suite(&DiskSuite{mem: false})
var _ = Suite(&DiskSuite{mem: true})

var diskPath = "/tmp/test-disk"

const diskSize uint64 = 100

func (suite *DiskSuite) SetUpTest(c *C) {
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

func (suite *DiskSuite) TearDownTest(c *C) {
	suite.D.Close()
	_ = os.Remove(diskPath)
}

var block0 Block = make([]byte, BlockSize)
var block1 Block = make([]byte, BlockSize)
var block2 Block = make([]byte, BlockSize)

func init() {
	block1[0] = 1
	block2[0] = 2
	diskPath += fmt.Sprintf(".%d", time.Now().UnixNano()/1000%1000)
}

func (suite *DiskSuite) TestReadWrite(c *C) {
	Write(3, block1)
	Write(4, block2)
	c.Check(Read(2), DeepEquals, block0)
	c.Check(Read(3), DeepEquals, block1)
	c.Check(Read(4), DeepEquals, block2)
}

func (suite *DiskSuite) TestSize(c *C) {
	c.Check(Size(), Equals, uint64(100))
}

func (suite *DiskSuite) TestBarrier(c *C) {
	Write(99, block1)
	Barrier()
	c.Check(Read(99), DeepEquals, block1)
}

func (suite *DiskSuite) TestCrash(c *C) {
	if suite.mem {
		// this test doesn't make sense on an in-memory disk
		return
	}

	Write(2, block1)
	Barrier()

	suite.D.Close()
	suite.SetUpTest(c)

	c.Check(Read(2), DeepEquals, block1)
	c.Check(Read(3), DeepEquals, block0)
}

func (suite *DiskSuite) TestModifyReadBlock(c *C) {
	Write(0, block0)
	b := Read(0)
	b[0] = 1
	c.Check(Read(0)[0], DeepEquals, byte(0))
}

func (suite *DiskSuite) TestModifyWriteBlock(c *C) {
	b := make([]byte, 4096)
	Write(0, b)
	b[0] = 1
	c.Check(Read(0)[0], DeepEquals, byte(0))
}

func (suite *DiskSuite) TestReadOob(c *C) {
	c.Assert(func() { Read(diskSize) }, PanicMatches, ".*out-of-bounds read.*")
}

func (suite *DiskSuite) TestWriteOob(c *C) {
	c.Assert(func() { Write(diskSize, block0) }, PanicMatches,
		".*out-of-bounds write.*")
}
