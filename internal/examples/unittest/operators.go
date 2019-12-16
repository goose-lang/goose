package unittest

func LogicalOperators(b1 bool, b2 bool) bool {
	return b1 && (b2 || b1) && !false
}

func ArithmeticShifts(x uint32, y uint64) uint64 {
	return uint64(x<<3) + (y << uint64(x)) + (y << 1)
}

func BitwiseOps(x uint32, y uint64) uint64 {
	return uint64(x) | uint64(uint32(y))&43
}

func Comparison(x uint64, y uint64) bool {
	if x < y {
		return true
	}
	if x == y {
		return true
	}
	if x != y {
		return true
	}
	if x > y {
		return true
	}
	if x+1 > y-2 {
		return true
	}
	return false
}
