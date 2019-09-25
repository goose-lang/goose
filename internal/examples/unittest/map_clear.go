package unittest

func clearMap(m map[uint64]uint64) {
	for k := range m {
		delete(m, k)
	}
}
