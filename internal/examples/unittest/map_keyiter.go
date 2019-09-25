package unittest

func IterateMapKeys(m map[uint64]uint64, sum *uint64) {
	for k := range m {
		oldSum := *sum
		*sum = oldSum + k
	}
}
