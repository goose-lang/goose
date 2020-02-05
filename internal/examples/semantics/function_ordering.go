package semantics

// helpers

// advances the array editor, and returns the value it wrote, storing
// "next" in next_val
func (ae *ArrayEditor) AdvanceReturn(next uint64) uint64 {
	var tmp = ae.next_val
	ae.s[0] = tmp
	ae.next_val = next
	ae.s = ae.s[1:]
	return tmp
}

// we call this function with side-effectful function calls as arguments,
// its implementation is unimportant
func addFour64(a uint64, b uint64, c uint64, d uint64) uint64 {
	return a + b + c + d
}

type Pair struct {
	x uint64
	y uint64
}

// tests
func testFunctionOrdering() bool {
	var arr = make([]uint64, 5)

	ae1 := ArrayEditor{s: arr[0:], next_val: 1}
	ae2 := ArrayEditor{s: arr[0:], next_val: 101}

	if ae1.AdvanceReturn(2)+ae2.AdvanceReturn(102) != 102 {
		return false
	}
	// ae2.AdvanceReturn should be called second.
	if arr[0] != 101 {
		return false
	}

	if addFour64(ae1.AdvanceReturn(3),
		ae2.AdvanceReturn(103),
		ae2.AdvanceReturn(104),
		ae1.AdvanceReturn(4)) != 210 {
		return false
	}

	if arr[1] != 102 {
		return false
	}

	if arr[2] != 3 {
		return false
	}

	// function calls in struct initializer
	p := Pair{x: ae1.AdvanceReturn(5), y: ae2.AdvanceReturn(105)}
	if arr[3] != 104 {
		return false
	}

	// y initializer executes first if listed first
	q := Pair{y: ae1.AdvanceReturn(6), x: ae2.AdvanceReturn(106)}
	if arr[4] != 105 {
		return false
	}
	return p.x+q.x == 109
}
