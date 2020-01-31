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

func testEncDec32Simple() bool {
	v0 := roundtripEncDec32(0) == 0
	v1 := roundtripEncDec32(1) == 1
	v2 := roundtripEncDec32(1231234) == 1231234
	return v0 && v1 && v2
}

func testEncDec32() bool {
	v0 := roundtripEncDec32(0xCCBB00AA) == 0xCCBB00AA
	v1 := roundtripEncDec32(1<<20) == 1<<20
	v2 := roundtripEncDec32(1<<18) == 1<<18
	v3 := roundtripEncDec32(1<<10) == 1<<10
	v4 := roundtripEncDec32(1<<0) == 1<<0
	v5 := roundtripEncDec32(1<<32 - 1) == 1<<32 - 1
	return v0 && v1 && v2 && v3 && v4 && v5
}

func roundtripEncDec64(x uint64) uint64 {
	r := make([]byte, 8)
	e := &Enc{p: r}
	d := &Dec{p: r}
	e.UInt64(x)
	return d.UInt64()
}

func testEncDec64Simple() bool {
	v0 := roundtripEncDec64(0) == 0
	v1 := roundtripEncDec64(1) == 1
	v2 := roundtripEncDec64(1231234) == 1231234
	return v0 && v1 && v2
}

func testEncDec64() bool {
	v0 := roundtripEncDec64(0xDD00CC00BB00AA) == 0xDD00CC00BB00AA
	v1 := roundtripEncDec64(1<<63) == 1<<63
	v2 := roundtripEncDec64(1<<47) == 1<<47
	v3 := roundtripEncDec64(1<<20) == 1<<20
	v4 := roundtripEncDec64(1<<18) == 1<<18
	v5 := roundtripEncDec64(1<<10) == 1<<10
	v6 := roundtripEncDec64(1<<0) == 1<<0
	v7 := roundtripEncDec64(1<<64 - 1) == 1<<64 - 1
	return v0 && v1 && v2 && v3 && v4 && v5 && v6 && v7
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

func testReverseAssignOps64() bool {
	v0 := roundtripEncDec64(0) == 0
	v1 := roundtripEncDec64(1) == 1
	v2 := roundtripEncDec64(1231234) == 1231234
	v3 := roundtripEncDec64(0xDD00CC00BB00AA) == 0xDD00CC00BB00AA
	v4 := roundtripEncDec64(1<<63) == 1<<63
	v5 := roundtripEncDec64(1<<47) == 1<<47
	v6 := roundtripEncDec64(1<<20) == 1<<20
	v7 := roundtripEncDec64(1<<18) == 1<<18
	v8 := roundtripEncDec64(1<<10) == 1<<10
	v9 := roundtripEncDec64(1<<0) == 1<<0
	v10 := roundtripEncDec64(1<<64 - 1) == 1<<64 - 1
	return v0 && v1 && v2 && v3 && v4 && v5 && v6 && v7 && v8 && v9 && v10
}

func reverseAssignOps32(x uint32) uint32 {
	var y uint32
	y += x
	y -= x
	y++
	y--
	return y
}

func testReverseAssignOps32() bool {
	v0 := roundtripEncDec32(0) == 0
	v1 := roundtripEncDec32(1) == 1
	v2 := roundtripEncDec32(1231234) == 1231234
	v3 := roundtripEncDec32(0xCCBB00AA) == 0xCCBB00AA
	v4 := roundtripEncDec32(1<<20) == 1<<20
	v5 := roundtripEncDec32(1<<18) == 1<<18
	v6 := roundtripEncDec32(1<<10) == 1<<10
	v7 := roundtripEncDec32(1<<0) == 1<<0
	v8 := roundtripEncDec32(1<<32 - 1) == 1<<32 - 1
	return v0 && v1 && v2 && v3 && v4 && v5 && v6 && v7 && v8
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
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}

	if CheckTrue(b) && CheckFalse(b) {
		return false
	}
	return b.tc == 1 && b.fc == 1
}

func testShortcircuitAndFT() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}

	if CheckFalse(b) && CheckTrue(b) {
		return false
	}
	return b.tc == 0 && b.fc == 1
}

func testShortcircuitOrTF() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}
	if CheckTrue(b) || CheckFalse(b) {
		return b.tc == 1 && b.fc == 0
	}
	return false
}

func testShortcircuitOrFT() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}
	if CheckFalse(b) || CheckTrue(b) {
		return b.tc == 1 && b.fc == 1
	}
	return false
}

// test integer overflow and underflow
func add64Equals(x uint64, y uint64, z uint64) bool {
	return x+y == z
}
func testAdd64Equals() bool {
	x := add64Equals(2, 3, 5)
	y := add64Equals(1<<64 - 1, 1, 0)
	return x && y
}

func minus64Equals(x uint64, y uint64, z uint64) bool {
	return x-y == z
}
func testMinus64Equals() bool {
	x := minus64Equals(2, 1, 1)
	y := minus64Equals(1<<64 - 1, 1 << 63, 1<<63 - 1)
	z := minus64Equals(2, 8, 1<<64 - 6)
	return x && y && z
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
	var arr = make([]uint64, 4)

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
	return p.x+q.x == 109
}

func testStandardForLoop() bool {
	var arr = make([]uint64, 4)
	arr[0] += 1
	arr[1] += 3
	arr[2] += 5
	arr[3] += 7
	return standardForLoop(arr) == 16
}

func testConditionalAssign() bool {
	return (conditionalAssign(true) == 2 && conditionalAssign(false) == 3)
}

func testConversions() bool {
	s := "four"
	b := stringToByteSlice(s)
	x := literalCast()
	return (x == uint64(len(b)) && byteSliceToString(b) == s)
}
