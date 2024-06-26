package semantics

func testAssignAddSub() bool {
	var ok = true
	var x uint64 = 1
	x += 5
	ok = ok && x == 6
	x -= 3
	ok = ok && x == 3
	return ok
}

func testAssignBitwise() bool {
	var ok = true
	var x uint64 = 123
	x |= 0x1f
	ok = ok && x == 123|0x1f
	x &= 0xf
	ok = ok && x == (123|0x1f)&0xf
	x ^= 0xaa
	ok = ok && x == ((123|0x1f)&0xf)^0xaa
	return ok
}
