package unittest

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

// TODO: separate GooseLang semantics tests from simpler syntactic unit tests

func TestEncDec32(t *testing.T) {
	for _, x := range []uint32{
		0, 1, 1231234, 0xCCBB00AA,
		1<<20 | 1<<18 | 1<<10 | 1<<0,
		1<<32 - 1,
	} {
		assert.True(t, EncDec32(x), "x: %v", x)
	}
}

func TestEncDec64(t *testing.T) {
	for _, x := range []uint64{
		0, 1, 1231234, 0xDD00CC00BB00AA,
		1<<63 | 1<<47 | 1<<20 | 1<<18 | 1<<10 | 1<<0,
		1<<64 - 1,
	} {
		assert.True(t, EncDec64(x), "x: %v", x)
	}
}
