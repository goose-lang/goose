package unittest

func ReturnTwo(p []byte) (uint64, uint64) {
	return 0, 0
}

func ReturnTwoWrapper(data []byte) (uint64, uint64) {
	a, b := ReturnTwo(data)
	return a, b
}
