package unittest

import (
	"testing"

	. "gopkg.in/check.v1"
)

// TODO: separate GooseLang semantics tests from simpler syntactic unit tests

func Test(t *testing.T) { TestingT(t) }

type TestSuite struct{}

var _ = Suite(&TestSuite{})

func (suite *TestSuite) TestEncDec32(c *C) {
	for _, x := range []uint32{
		0, 1, 1231234, 0xCCBB00AA,
		1<<20 | 1<<18 | 1<<10 | 1<<0,
		1<<32 - 1,
	} {
		c.Check(testEncDec32(x), Equals, true, Commentf("x: %v", x))
	}
}

func (suite *TestSuite) TestEncDec64(c *C) {
	for _, x := range []uint64{
		0, 1, 1231234, 0xDD00CC00BB00AA,
		1<<63 | 1<<47 | 1<<20 | 1<<18 | 1<<10 | 1<<0,
		1<<64 - 1,
	} {
		c.Check(testEncDec64(x), Equals, true, Commentf("x: %v", x))
	}
}

func (suite *TestSuite) TestReverseAssignOps32(c *C) {
	for _, x := range []uint32{
		0, 1, 1231234, 0xCCBB00AA,
		1<<20 | 1<<18 | 1<<10 | 1<<0,
		1<<32 - 1,
	} {
		c.Check(testReverseAssignOps32(x), Equals, true, Commentf("x: %v", x))
	}
}

func (suite *TestSuite) TestReverseAssignOps64(c *C) {
	for _, x := range []uint64{
		0, 1, 1231234, 0xDD00CC00BB00AA,
		1<<63 | 1<<47 | 1<<20 | 1<<18 | 1<<10 | 1<<0,
		1<<64 - 1,
	} {
		c.Check(testReverseAssignOps64(x), Equals, true, Commentf("x: %v", x))
	}
}

func (suite *TestSuite) TestAdd64Equals(c *C) {
	tests := []struct {
		x uint64
		y uint64
		z uint64
	}{
		{1, 1, 2},
		{1<<64 - 1, 1, 0},
		{2, 8, 10},
	}
	for _, t := range tests {
		c.Check(testAdd64Equals(t.x, t.y, t.z), Equals, true, Commentf("x: %v, y: %v, expected result: %v", t.x, t.y, t.z))
	}
}

func (suite *TestSuite) TestMinus64Equals(c *C) {
	tests := []struct {
		x uint64
		y uint64
		z uint64
	}{
		{2, 1, 1},
		{1<<64 - 1, 1 << 63, 1<<63 - 1},
		{2, 8, 1<<64 - 6},
	}
	for _, t := range tests {
		c.Check(testMinus64Equals(t.x, t.y, t.z), Equals, true, Commentf("x: %v, y: %v, expected result: %v", t.x, t.y, t.z))
	}
}

func (suite *TestSuite) TestShortcircuitAndTF(c *C) {
	c.Check(testShortcircuitAndTF(), Equals, true)
}

func (suite *TestSuite) TestShortcircuitAndFT(c *C) {
	c.Check(testShortcircuitAndFT(), Equals, true)
}

func (suite *TestSuite) TestShortcircuitOrTF(c *C) {
	c.Check(testShortcircuitOrTF(), Equals, true)
}

func (suite *TestSuite) TestShortcircuitOrFT(c *C) {
	c.Check(testShortcircuitOrFT(), Equals, true)
}

func (suite *TestSuite) TestOverwriteArray(c *C) {
	c.Check(testOverwriteArray(), Equals, true, Commentf("failed"))
}

func (suite *TestSuite) TestFunctionOrdering(c *C) {
	c.Check(testFunctionOrdering(), Equals, true, Commentf("failed"))
}

func (suite *TestSuite) TestStandardForLoop(c *C) {
	c.Check(testStandardForLoop(), Equals, true, Commentf("failed"))
}
