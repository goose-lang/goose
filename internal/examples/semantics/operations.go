package semantics

// helpers
func reverseAssignOps64(x uint64) uint64 {
	var y uint64
	y += x
	y -= x
	y++
	y--
	return y
}

func reverseAssignOps32(x uint32) uint32 {
	var y uint32
	y += x
	y -= x
	y++
	y--
	return y
}

func add64Equals(x uint64, y uint64, z uint64) bool {
	return x+y == z
}

func sub64Equals(x uint64, y uint64, z uint64) bool {
	return x-y == z
}

// tests
func testReverseAssignOps64() bool {
	var ok = true
	ok = ok && (reverseAssignOps64(0) == 0)
	ok = ok && (reverseAssignOps64(1) == 0)
	ok = ok && (reverseAssignOps64(1231234) == 0)
	ok = ok && (reverseAssignOps64(0xDD00CC00BB00AA) == 0)
	ok = ok && (reverseAssignOps64(1<<63) == 0)
	ok = ok && (reverseAssignOps64(1<<47) == 0)
	ok = ok && (reverseAssignOps64(1<<20) == 0)
	ok = ok && (reverseAssignOps64(1<<18) == 0)
	ok = ok && (reverseAssignOps64(1<<10) == 0)
	ok = ok && (reverseAssignOps64(1<<0) == 0)
	ok = ok && (reverseAssignOps64(1<<64-1) == 0)
	return ok
}

func failing_testReverseAssignOps32() bool {
	var ok = true
	ok = ok && (reverseAssignOps32(0) == 0)
	ok = ok && (reverseAssignOps32(1) == 0)
	ok = ok && (reverseAssignOps32(1231234) == 0)
	ok = ok && (reverseAssignOps32(0xCCBB00AA) == 0)
	ok = ok && (reverseAssignOps32(1<<20) == 0)
	ok = ok && (reverseAssignOps32(1<<18) == 0)
	ok = ok && (reverseAssignOps32(1<<10) == 0)
	ok = ok && (reverseAssignOps32(1<<0) == 0)
	ok = ok && (reverseAssignOps32(1<<32-1) == 0)
	return ok
}

func testAdd64Equals() bool {
	var ok = true
	ok = ok && add64Equals(2, 3, 5)
	ok = ok && add64Equals(1<<64-1, 1, 0)
	return ok
}

func testSub64Equals() bool {
	var ok = true
	ok = ok && sub64Equals(2, 1, 1)
	ok = ok && sub64Equals(1<<64-1, 1<<63, 1<<63-1)
	ok = ok && sub64Equals(2, 8, 1<<64-6)
	return ok
}

func failing_testDivisionPrecedence() bool {
	blockSize := uint64(4096)
	hdrmeta := uint64(8)
	hdraddrs := (blockSize - hdrmeta) / 8
	return hdraddrs == 511
}

func failing_testModPrecedence() bool {
	x1 := 513 + 12%8
	x2 := (513 + 12) % 8
	return x1 == 517 && x2 == 5
}
