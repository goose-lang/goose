package example

type Box[T any] struct { // ERROR generic named type
	v T
}
