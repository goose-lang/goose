// Package machine is a support library for operations on integers.
//
// Goose code can use these additional functions. They have corresponding
// primitives and a model in the Goose `Heap.v` model of Go's built-in heap data
// structures, under the `Data` module.
package machine

import (
	"encoding/binary"
	"fmt"
	"math/rand"
)

// UInt64Get converts the first 8 bytes of p to a uint64.
//
// Requires p be at least 8 bytes long.
//
// Happens to decode in little-endian byte order, but this is only relevant as
// far as the relationship between UInt64Get and UInt64Encode.
func UInt64Get(p []byte) uint64 {
	return binary.LittleEndian.Uint64(p)
}

// UInt64Put stores n to the first 8 bytes of p
//
// Requires p to be at least 8 bytes long.
//
// Uses little-endian byte order, but this is only relevant in that it's the
// inverse of UInt64Get.
func UInt64Put(p []byte, n uint64) {
	binary.LittleEndian.PutUint64(p, n)
}

// RandomUint64 returns a random uint64 using the global seed.
func RandomUint64() uint64 {
	return rand.Uint64()
}

// UInt64ToString formats a number as a string.
//
// Assumed to be pure and injective in the Coq model.
func UInt64ToString(x uint64) string {
	return fmt.Sprintf("%d", x)
}
