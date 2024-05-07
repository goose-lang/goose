package semantics

func testSingleAppend() bool {
	var ok bool = true
	var a []uint64
	a = append(a, 1)
	ok = ok && a[0] == 1
	return ok
}

func testAppendToCapacity() bool {
	var ok bool = true
	var a []uint64
	a = make([]uint64, 0, 1)
	a = append(a, 1)
	ok = ok && a[0] == 1
	return ok
}

func testAppendSlice() bool {
	var ok bool = true
	var a []uint64
	var b []uint64
	b = append(b, 1)
	b = append(b, 2)
	a = append(a, b...)
	ok = ok && a[0] == 1 && a[1] == 2
	return ok
}
