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

// UInt64Encode is a functional little-endian encoder, to mirror the Coq model.
//
// We could instead expose PutUint64 directly, but this would require another
// stateful function on byteslices.
func UInt64Encode(n uint64) []byte {
	p := make([]byte, 8)
	binary.LittleEndian.PutUint64(p, n)
	return p
}
