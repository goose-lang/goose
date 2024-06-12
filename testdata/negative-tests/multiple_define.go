package example

func multiassign() uint64 {
	x, y := uint64(0), uint64(0) // ERROR multiple
	return x + y
}
