package unittest

func conditionalReturn(x bool) uint64 {
	if x {
		return 0
	}
	return 1
}

func alwaysReturn(x bool) uint64 {
	if x {
		return 0
	} else {
		return 1
	}
}

func alwaysReturnInNestedBranches(x bool) uint64 {
	if !x {
		if x {
			return 0
		} else {
			return 1
		}
	} else {
		// we can even have an empty else block
	}
	y := uint64(14)
	return y
}

func earlyReturn(x bool) {
	if x {
		return
	}
}

func conditionalAssign(x bool) uint64 {
	var y uint64
	if x {
		y = 1
	} else {
		y = 2
	}
	y += 1
	return y
}

func elseIf(x, y bool) uint64 {
	if x {
		return 0
	} else if y {
		return 1
	} else {
		return 2
	}
}
