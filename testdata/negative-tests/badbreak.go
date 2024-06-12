package example

func sumSlice(xs []uint64) uint64 {
	var sum uint64
	for _, x := range xs {
		sum += x
		break // ERROR break/continue in unsupported position
	}
	return sum
}
