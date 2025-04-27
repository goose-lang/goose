package unittest

// Box is the simplest generic struct
type Box[T any] struct {
	Value T
}
type Container[T any] struct {
	// various uses of T inside a type
	X T
	Y map[int]T
	Z *T
	W uint64
}

// B does not have type parameters but requires instantiating a generic type
type UseContainer struct {
	X Container[uint64]
}

// OnlyIndirect can be modeled as a go_type without its type argument (due to
// the indirections)
type OnlyIndirect[T any] struct {
	X []T
	Y *T
}

// type IntMap[T any] map[uint64]T

/*
// MultiParam takes two type parameters
type MultiParam[A any, B any] struct {
	Y B
	X A
}
*/
