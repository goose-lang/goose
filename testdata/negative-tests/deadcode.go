package example

func codeAfterReturn(m map[uint64]uint64) uint64 {
	return 0 // ERROR return in unsupported position
	m[1] = 1
	return 1
}
