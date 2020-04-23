package semantics

func failing_testOrCompareSimple() bool {
	if 3 > 4 || 4 > 3 {
		return true
	}
	return false
}

func failing_testOrCompare() bool {
	var ok = true
	if !(3 > 4 || 4 > 3) {
		ok = false
	}
	if 3 > 4 || 2 > 3 {
		ok = false
	} else {
	}
	return ok
}

func failing_testAndCompare() bool {
	var ok = true
	if 3 > 4 && 4 > 3 {
		ok = false
	}
	if 4 > 3 || 3 > 2 {
	} else {
		ok = false
	}
	return ok
}
