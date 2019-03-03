package unittest

func TypedLiteral() uint64 {
	return 3
}

func LiteralCast() uint64 {
	// produces a uint64 -> uint64 conversion
	x := uint64(2)
	return x + 2
}

func CastInt(p []byte) uint64 {
	return uint64(len(p))
}

func StringToByteSlice(s string) []byte {
	// must be lifted, impure operation
	p := []byte(s)
	return p
}

func ByteSliceToString(p []byte) string {
	// must be lifted, impure operation
	s := string(p)
	return s
}
