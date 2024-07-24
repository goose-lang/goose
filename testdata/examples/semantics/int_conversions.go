package semantics

func testU64ToU32() bool {
	var ok = true
	x := uint64(1230)
	y := uint32(1230)
	ok = ok && uint32(x) == y
	ok = ok && uint64(y) == x
	return ok
}

func testU32Len() bool {
	s := make([]byte, 100)
	return uint32(len(s)) == uint32(100)
}

type Uint32 uint32

// https://github.com/goose-lang/goose/issues/14
func failing_testU32NewtypeLen() bool {
	s := make([]byte, 20)
	return Uint32(len(s)) == Uint32(20)
}
