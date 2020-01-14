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
	D FileDisk
}

var _ = Suite(&DiskSuite{})

var diskPath = "/tmp/test-disk"

const diskSize uint64 = 100

func (suite *DiskSuite) SetUpTest(c *C) {
	d, err := NewFileDisk(diskPath, diskSize)
	if err != nil {
		panic(err)
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
	Write(2, block1)
	Barrier()

	suite.D.Close()
	d, err := NewFileDisk(diskPath, diskSize)
	if err != nil {
		panic(err)
	}
	suite.D = d
	Init(suite.D)

	c.Check(Read(2), DeepEquals, block1)
	c.Check(Read(3), DeepEquals, block0)
}
