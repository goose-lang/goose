package records

// A generic hash function signature, instantiate with something that distributes well.
type HashFn func([]byte) uint32

// A naive hash function that is trivial to verify.
func SumHash(key []byte) uint32 {
	var sum uint32
	for _, b := range key {
		sum += uint32(b)
	}
	return sum
}

// Assign one of num_partitions to key using hash.
func Partition(key []byte, num_partitions uint32, hash HashFn) uint32 {
	return hash(key) % num_partitions
}
