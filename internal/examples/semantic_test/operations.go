package semantic_test

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
	ok := true
	ok = ok && (reverseAssignOps64(0) == 0)
	ok = ok && (reverseAssignOps64(1) == 1)
	ok = ok && (reverseAssignOps64(1231234) == 1231234)
	ok = ok && (reverseAssignOps64(0xDD00CC00BB00AA) == 0xDD00CC00BB00AA)
	ok = ok && (reverseAssignOps64(1<<63) == 1<<63)
	ok = ok && (reverseAssignOps64(1<<47) == 1<<47)
	ok = ok && (reverseAssignOps64(1<<20) == 1<<20)
	ok = ok && (reverseAssignOps64(1<<18) == 1<<18)
	ok = ok && (reverseAssignOps64(1<<10) == 1<<10)
	ok = ok && (reverseAssignOps64(1<<0) == 1<<0)
	ok = ok && (reverseAssignOps64(1<<64-1) == 1<<64-1)
        return ok
}

func testReverseAssignOps32() bool {
	ok := true
	ok = ok && (reverseAssignOps32(0) == 0)
	ok = ok && (reverseAssignOps32(1) == 1)
	ok = ok && (reverseAssignOps32(1231234) == 1231234)
	ok = ok && (reverseAssignOps32(0xCCBB00AA) == 0xCCBB00AA)
	ok = ok && (reverseAssignOps32(1<<20) == 1<<20)
	ok = ok && (reverseAssignOps32(1<<18) == 1<<18)
	ok = ok && (reverseAssignOps32(1<<10) == 1<<10)
	ok = ok && (reverseAssignOps32(1<<0) == 1<<0)
	ok = ok && (reverseAssignOps32(1<<32-1) == 1<<32-1)
	return ok
}

func testAdd64Equals() bool {
	ok := true
	ok = ok && add64Equals(2, 3, 5)
	ok = ok && add64Equals(1<<64-1, 1, 0)
	return ok
}

func testSub64Equals() bool {
	ok := true
	ok = ok && sub64Equals(2, 1, 1)
	ok = ok && sub64Equals(1<<64-1, 1<<63, 1<<63-1)
	ok = ok && sub64Equals(2, 8, 1<<64-6)
	return ok
}
