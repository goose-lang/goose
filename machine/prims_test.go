package machine

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestUInt64GetPut(t *testing.T) {
	assert := assert.New(t)
	tests := []uint64{
		0, 1, ^uint64(1),
		13 << 30,
		13 << 10,
		0xfc<<30 | 0xb<<20 | 0xa<<10 | 0x1,
	}
	for _, tt := range tests {
		p := make([]byte, 8)
		UInt64Put(p, tt)
		assert.Equal(tt, UInt64Get(p))
	}
	for _, tt := range tests {
		p := make([]byte, 10)
		UInt64Put(p, tt)
		assert.Equal(tt, UInt64Get(p), "with larger buffer")
	}
}

func TestUInt32GetPut(t *testing.T) {
	assert := assert.New(t)
	tests := []uint32{
		0, 1, ^uint32(1),
		13 << 15,
		13 << 5,
		0xfc<<15 | 0xb<<10 | 0xa<<5 | 0x1,
	}
	for _, tt := range tests {
		p := make([]byte, 4)
		UInt32Put(p, tt)
		assert.Equal(tt, UInt32Get(p))
	}
	for _, tt := range tests {
		p := make([]byte, 10)
		UInt32Put(p, tt)
		assert.Equal(tt, UInt32Get(p), "with larger buffer")
	}
}

func TestUInt64ToString(t *testing.T) {
	assert := assert.New(t)
	tests := []struct {
		Num uint64
		Str string
	}{
		{0, "0"},
		{2, "2"},
		{1024, "1024"},
	}
	for _, tt := range tests {
		assert.Equal(tt.Str, UInt64ToString(tt.Num))
	}
}

func TestRandomDoesNotPanic(t *testing.T) {
	// not much we can test here
	RandomUint64()
	RandomUint64()
}
