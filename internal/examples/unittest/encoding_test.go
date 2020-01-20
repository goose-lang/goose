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
		c.Check(EncDec32(x), Equals, true)
	}
}

func (suite *TestSuite) TestEncDec64(c *C) {
	for _, x := range []uint64{
		0, 1, 1231234, 0xDD00CC00BB00AA,
		1<<63 | 1<<47 | 1<<20 | 1<<18 | 1<<10 | 1<<0,
		1<<64 - 1,
	} {
		c.Check(EncDec64(x), Equals, true)
	}
}
