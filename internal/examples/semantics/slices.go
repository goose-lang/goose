package semantics

// helpers
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

// tests
func testOverwriteArray() bool {
	var arr = make([]uint64, 4)

	ae1 := &ArrayEditor{s: arr[0:], next_val: 1}
	ae2 := &ArrayEditor{s: arr[1:], next_val: 102}
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
