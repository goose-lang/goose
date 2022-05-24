package generic

func SliceMap[T, U any](f func(T) U, s []T) []U {
	var newSlice []U
	for _, x := range s {
		newSlice = append(newSlice, f(x))
	}
	return newSlice
}

func Id[T any](x T) T {
	return x
}

func MapLen[V any](m map[uint64]V) uint64 {
	return uint64(len(m))
}
