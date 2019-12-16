package unittest

func clearMap(m map[uint64]uint64) {
	for k := range m {
		delete(m, k)
	}
}

func IterateMapKeys(m map[uint64]uint64, sum *uint64) {
	for k := range m {
		oldSum := *sum
		*sum = oldSum + k
	}
}

func MapSize(m map[uint64]bool) uint64 {
	return uint64(len(m))
}
