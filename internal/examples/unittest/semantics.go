package unittest

// TODO: organize these tests into separate files

// test that encoding and decoding roundtrips
func roundtripEncDec32(x uint32) uint32 {
	r := make([]byte, 4)
	e := &Enc{p: r}
	d := &Dec{p: r}
	e.UInt32(x)
	return d.UInt32()
}

func testEncDec32(x uint32) bool {
	return roundtripEncDec32(x) == x
}

func roundtripEncDec64(x uint64) uint64 {
	r := make([]byte, 8)
	e := &Enc{p: r}
	d := &Dec{p: r}
	e.UInt64(x)
	return d.UInt64()
}

func testEncDec64(x uint64) bool {
	return roundtripEncDec64(x) == x
}

// test that y defaults to 0 and subtraction always reverses addition
func reverseAssignOps64(x uint64) uint64 {
	var y uint64
	y += x
	y -= x
	y++
	y--
	return y
}

func testReverseAssignOps64(x uint64) bool {
	return reverseAssignOps64(x) == 0
}

func reverseAssignOps32(x uint32) uint32 {
	var y uint32
	y += x
	y -= x
	y++
	y--
	return y
}

func testReverseAssignOps32(x uint32) bool {
	return reverseAssignOps32(x) == 0
}

// test shortcircuiting behaviors for logical operators
type BoolTest struct {
	t  bool
	f  bool
	tc uint64
	fc uint64
}

func CheckTrue(b *BoolTest) bool {
	b.tc += 1
	return b.t
}

func CheckFalse(b *BoolTest) bool {
	b.fc += 1
	return b.f
}

func testShortcircuitAndTF() bool {
	b := BoolTest{t: true, f: false, tc: 0, fc: 0}

	if CheckTrue(&b) && CheckFalse(&b) {
		return false
	}
	return (b.tc == 1 && b.fc == 1)
}

func testShortcircuitAndFT() bool {
	b := BoolTest{t: true, f: false, tc: 0, fc: 0}

	if CheckFalse(&b) && CheckTrue(&b) {
		return false
	}
	return (b.tc == 0) && (b.fc == 1)
}

func testShortcircuitOrTF() bool {
	b := BoolTest{t: true, f: false, tc: 0, fc: 0}
	if CheckTrue(&b) || CheckFalse(&b) {
		return (b.tc == 1 && b.fc == 0)
	}
	return false
}

func testShortcircuitOrFT() bool {
	b := BoolTest{t: true, f: false, tc: 0, fc: 0}
	if CheckFalse(&b) || CheckTrue(&b) {
		return (b.tc == 1 && b.fc == 1)
	}
	return false
}

// test integer overflow and underflow
func testAdd64Equals(x uint64, y uint64, z uint64) bool {
	return x+y == z
}

func testMinus64Equals(x uint64, y uint64, z uint64) bool {
	return x-y == z
}

// test side-effects on array writes from multiple accessors
type ArrayEditor struct {
	s        []uint64
	next_val uint64
}

func (ae *ArrayEditor) Advance(arr []uint64, next uint64) {
	arr[0] += 1
	ae.s[0] = ae.next_val
	ae.next_val = next
	ae.s = ae.s[1:]
}

func testOverwriteArray() bool {
	var arr []uint64 = make([]uint64, 4)

	ae1 := ArrayEditor{s: arr[0:], next_val: 1}
	ae2 := ArrayEditor{s: arr[1:], next_val: 102}
	ae2.Advance(arr, 103)
	ae2.Advance(arr, 104)
	ae2.Advance(arr, 105) // 105 never gets written to array

	ae1.Advance(arr, 2) // resets arr[0]
	ae1.Advance(arr, 3)
	ae1.Advance(arr, 4)
	ae1.Advance(arr, 5) // 5 never written to array

	// make sure all values were overwritten properly
	if arr[0]+arr[1]+arr[2]+arr[3] >= 100 {
		return false
	}
	return arr[3] == 4 && arr[0] == 4
}

// test ordering of function calls with side effects

// advances the array editor, and returns the value it wrote, storing "next" in next_val
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

func testFunctionOrdering() bool {
	var arr []uint64 = make([]uint64, 5)

	ae1 := ArrayEditor{s: arr[0:], next_val: 1}
	ae2 := ArrayEditor{s: arr[0:], next_val: 101}

	if ae1.AdvanceReturn(2)+ae2.AdvanceReturn(102) != 102 {
		return false
	}
	// ae2.AdvanceReturn should be called second.
	if arr[0] != 101 {
		return false
	}

	if addFour64(ae1.AdvanceReturn(3), ae2.AdvanceReturn(103), ae2.AdvanceReturn(104), ae1.AdvanceReturn(4)) != 210 {
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
	return (p.x+q.x == 109)
}
