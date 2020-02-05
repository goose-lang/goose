package semantics

// helpers

func literalCast() uint64 {
	// produces a uint64 -> uint64 conversion
	x := uint64(2)
	return x + 2
}

func stringToByteSlice(s string) []byte {
	// must be lifted, impure operation
	p := []byte(s)
	return p
}

func byteSliceToString(p []byte) string {
	// must be lifted, impure operation
	s := string(p)
	return s
}

// tests
func testConversions() bool {
	s := "four"
	b := stringToByteSlice(s)
	x := literalCast()
	return (x == uint64(len(b)) && byteSliceToString(b) == s)
}
