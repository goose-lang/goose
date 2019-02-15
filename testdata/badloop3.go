package example

func MissingLoopAssign() {
	for i := uint64(0); ; {
		if i < 4 {
			// only break is supported
			continue
		}
		break
	}
}
