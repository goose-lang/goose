package unittest

type LinkedList struct {
	Value int
	Next  *LinkedList
}

type Box[T any] struct {
	Value *T
}

type List struct {
	Value int
	Next  Box[List]
}
