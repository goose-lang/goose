package unittest

type stringWrapper string

func typedLiteral() uint64 {
	return 3
}

func literalCast() uint64 {
	// produces a uint64 -> uint64 conversion
	x := uint64(2)
	return x + 2
}

func castInt(p []byte) uint64 {
	return uint64(len(p))
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

// TODO: this results in a call to the type alias,
//  which doesn't make sense in Coq
/*
func stringToStringWrapper(s string) stringWrapper {
	return stringWrapper(s)
}
*/

func stringWrapperToString(s stringWrapper) string {
	return string(s)
}
