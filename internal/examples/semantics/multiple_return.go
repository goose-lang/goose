package semantics

func returnTwo() (uint64, uint64) {
	return 2, 3
}

func testReturnTwo() bool {
	x, y := returnTwo()
	return x == 2 && y == 3
}

func testAnonymousBinding() bool {
	_, y := returnTwo()
	return y == 3
}

func returnThree() (uint64, bool, uint32) {
	return 2, true, 1
}

func failing_testReturnThree() bool {
	x, y, z := returnThree()
	return x == 2 && y == true && z == 1
}
