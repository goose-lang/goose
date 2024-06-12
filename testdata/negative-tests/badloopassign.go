package example

func badLoopAssign() {
	k := make(map[uint64]uint64)
	for i := uint64(0); ; {
		if i < 3 {
			k[i] = i // need to use k
			k = nil  // ERROR variable k is not assignable
			continue
		} else {
			break
		}
	}
}
