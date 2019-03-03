package unittest

func returnTwo(p []byte) (uint64, uint64) {
	return 0, 0
}

func returnTwoWrapper(data []byte) (uint64, uint64) {
	a, b := returnTwo(data)
	return a, b
}
