package semantics

// helpers
func standardForLoop(s []uint64) uint64 {
	// this is the boilerplate needed to do a normal for loop
	sumPtr := new(uint64)
	for i := uint64(0); ; {
		if i < uint64(len(s)) {
			// the body of the loop
			sum := *sumPtr
			x := s[i]
			*sumPtr = sum + x

			i = i + 1
			continue
		}
		break
	}
	sum := *sumPtr
	return sum
}

// tests
func testStandardForLoop() bool {
	var arr = make([]uint64, 4)
	arr[0] += 1
	arr[1] += 3
	arr[2] += 5
	arr[3] += 7
	return standardForLoop(arr) == 16
}
