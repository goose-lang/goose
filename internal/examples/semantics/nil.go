package semantics

func failing_testCompareSliceToNil() bool {
	s := make([]byte, 0)
	return s != nil
}

func testComparePointerToNil() bool {
	s := new(uint64)
	return s != nil
}

func testCompareNilToNil() bool {
	s := new(*uint64)
	return *s == nil
}

func testComparePointerWrappedToNil() bool {
	var s []byte
	s = make([]byte, 1)
	return s != nil
}

func testComparePointerWrappedDefaultToNil() bool {
	var s []byte
	return s == nil
}
