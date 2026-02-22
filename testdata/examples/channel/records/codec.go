package records

import (
	"bytes"
	"encoding/binary"
)

// Codec translates a typed record to/from bytes.
// The encoded form is a single flat []byte; outer framing provides lengths.
type Codec[K any, V any] interface {
	// Size returns the encoded length of the record without allocating.
	Size(k K, v V) int
	// Marshal encodes the full record onto dst and returns the extended slice.
	Marshal(dst []byte, k K, v V) []byte
	// MarshalKey encodes only the key onto dst and returns the extended slice.
	MarshalKey(dst []byte, k K) []byte
	// MarshalVal encodes only the value onto dst and returns the extended slice.
	MarshalVal(dst []byte, v V) []byte
	// Unmarshal decodes a record from the full encoded slice for that record.
	Unmarshal(src []byte) (K, V, error)
	UnmarshalKey(src []byte) (K, error)
	UnmarshalVal(src []byte) (V, error)
	// KeyBytes returns a slice of the key bytes within an encoded record,
	// without allocating. Used for hashing and comparison.
	KeyBytes(src []byte) []byte
	// Compare compares two encoded records by key. Implementations should
	// avoid unmarshaling if the key bytes can be compared directly.
	Compare(a, b []byte) int
}

// -------------------- Word count (string → uint32) --------------------

// WordCountCodec encodes a (string, uint32) record as:
//
//	[2 bytes key length][key bytes][4 bytes value]
type WordCountCodec struct{}

const wcValSize = 4
const wcLenSize = 2

func (WordCountCodec) Size(k string, v uint32) int {
	return wcLenSize + len(k) + wcValSize
}

func (WordCountCodec) Marshal(dst []byte, k string, v uint32) []byte {
	dst = binary.LittleEndian.AppendUint16(dst, uint16(len(k)))
	dst = append(dst, k...)
	dst = binary.LittleEndian.AppendUint32(dst, v)
	return dst
}

func (WordCountCodec) MarshalKey(dst []byte, k string) []byte {
	return append(dst, k...)
}

func (WordCountCodec) MarshalVal(dst []byte, v uint32) []byte {
	return binary.LittleEndian.AppendUint32(dst, v)
}

func (WordCountCodec) Unmarshal(src []byte) (string, uint32, error) {
	klen := int(binary.LittleEndian.Uint16(src))
	k := string(src[wcLenSize : wcLenSize+klen])
	// TODO: Put this back when we have utf8
	/*if !utf8.ValidString(k) {
		return "", 0, errors.New("key is not valid utf-8")
	}*/
	v := binary.LittleEndian.Uint32(src[wcLenSize+klen:])
	return k, v, nil
}

func (WordCountCodec) KeyBytes(src []byte) []byte {
	klen := int(binary.LittleEndian.Uint16(src))
	return src[wcLenSize : wcLenSize+klen]
}

func (WordCountCodec) Compare(a, b []byte) int {
	aLen := int(binary.LittleEndian.Uint16(a))
	bLen := int(binary.LittleEndian.Uint16(b))
	return bytes.Compare(
		a[wcLenSize:wcLenSize+aLen],
		b[wcLenSize:wcLenSize+bLen],
	)
}

func (WordCountCodec) UnmarshalKey(src []byte) (string, error) {
	k := string(src)
	/*
		if !utf8.ValidString(k) {
			return "", errors.New("key is not valid utf-8")
		}
	*/
	return k, nil
}

func (WordCountCodec) UnmarshalVal(src []byte) (uint32, error) {
	return binary.LittleEndian.Uint32(src), nil
}
