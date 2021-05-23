package example

func codeAfterReturn(m map[uint64]uint64) uint64 {
	return 0
	m[1] = 1 // ERROR following return
	return 1
}
