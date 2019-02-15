package example

func MissingLoopAssign() {
	for i := uint64(0); ; {
		if i < 4 {
			continue // ERROR only break is supported
		}
		break
	}
}
