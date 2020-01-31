package machine

import (
	"testing"

	. "gopkg.in/check.v1"
)

func Test(t *testing.T) { TestingT(t) }

type PrimSuite struct{}

var _ = Suite(&PrimSuite{})

func (s *PrimSuite) TestUInt64GetPut(c *C) {
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

func (s *PrimSuite) TestUInt32GetPut(c *C) {
	tests := []uint32{
		0, 1, ^uint32(1),
		13 << 15,
		13 << 5,
		0xfc<<15 | 0xb<<10 | 0xa<<5 | 0x1,
	}
	for _, tt := range tests {
		p := make([]byte, 4)
		UInt32Put(p, tt)
		c.Check(UInt32Get(p), Equals, tt)
	}
	for _, tt := range tests {
		p := make([]byte, 10)
		UInt32Put(p, tt)
		c.Check(UInt32Get(p), Equals, tt, Commentf("with larger buffer"))
	}
}

func (s *PrimSuite) TestUInt64ToString(c *C) {
	tests := []struct {
		Num uint64
		Str string
	}{
		{0, "0"},
		{2, "2"},
		{1024, "1024"},
	}
	for _, tt := range tests {
		c.Check(UInt64ToString(tt.Num), Equals, tt.Str)
	}
}

func (s *PrimSuite) TestRandomDoesNotPanic(c *C) {
	// not much we can test here
	RandomUint64()
	RandomUint64()
}
