package unittest

func typeAssertInt(x any) int {
	return x.(int)
}

func wrapUnwrapInt() int {
	return typeAssertInt(1)
}

func checkedTypeAssert(x any) uint64 {
	if v, ok := x.(uint64); ok {
		return v
	}
	return 3
}
