package machine

import "encoding/binary"

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
