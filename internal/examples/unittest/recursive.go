package unittest

func recur(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return n + recur(n-1)
}
