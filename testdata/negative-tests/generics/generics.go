package unittest

// identity is the simplest generic function
func identity[A any](a A) A { // ERROR generic functions not supported
	return a
}

func useIdentity() {
	identity[int](1)  // explicit type parameter
	identity("hello") // infer and pass type parameter
}

// Box is the simplest generic struct
type Box[T any] struct {
	Value T
}

func mkBox[T any](v T) Box[T] {
	return Box[T]{Value: v}
}

type Container[T any] struct {
	// various uses of T inside a type
	X T
	Y map[int]T
	Z *T
	W uint64
}

func useContainer() {
	container := Container[uint64]{X: 1, Y: map[int]uint64{1: 2}, Z: new(uint64), W: 3}
	container.X = 2
	container.Y[2] = 3
	container.Z = new(uint64)
	container.W = 4
}

// B does not have type parameters but requires instantiating a generic type
type UseContainer struct {
	X Container[uint64]
}

func genericG[T any](x Container[T], y Container[bool]) {
	*x.Z = x.X
	x.W = y.W
}

func useGenericG() {
	x := Container[uint64]{X: 1, Y: map[int]uint64{1: 2}, Z: new(uint64), W: 3}
	y := Container[bool]{X: true, Y: map[int]bool{1: false}, Z: new(bool), W: 4}
	genericG(x, y)
}

// OnlyIndirect can be modeled as a go_type without its type argument (due to
// the indirections)
type OnlyIndirect[T any] struct {
	X []T
	Y *T
}

type IntMap[T any] map[uint64]T

func useIntMap() {
	m := IntMap[uint64]{}
	m[1] = 2
}

// MultiParam takes two type parameters
type MultiParam[A any, B any] struct {
	Y B
	X A
}

func useMultiParam() {
	mp := MultiParam[uint64, bool]{Y: true, X: 1}
	mp.X = 2
}

func swapMultiParam[A any](p *MultiParam[A, A]) {
	temp := p.X
	p.X = p.Y
	p.Y = temp
}

func multiParamFunc[A any, B any](x A, b B) []B {
	return []B{b}
}

func useMultiParamFunc() {
	multiParamFunc[uint64, bool](1, true)
}
