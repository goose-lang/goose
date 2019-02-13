package machine

import (
	"testing"

	. "gopkg.in/check.v1"
)

func Test(t *testing.T) { TestingT(t) }

type PrimSuite struct{}

var _ = Suite(&PrimSuite{})

func (s PrimSuite) TestUInt64GetPut(c *C) {
	tests := []uint64{
		0, 1, ^uint64(1),
		13 << 30,
		13 << 10,
		0xfc<<30 | 0xb<<20 | 0xa<<10 | 0x1,
	}
	for _, tt := range tests {
		p := make([]byte, 8)
		UInt64Put(p, tt)
		c.Check(UInt64Get(p), Equals, tt)
	}
	for _, tt := range tests {
		p := make([]byte, 10)
		UInt64Put(p, tt)
		c.Check(UInt64Get(p), Equals, tt, Commentf("with larger buffer"))
	}
}
