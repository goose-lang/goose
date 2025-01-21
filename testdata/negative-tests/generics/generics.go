package semantics

type genericStruct[A any, B any] struct {
	x A
	y B
}

type genericStruct2[T any] struct {
	g T
}

type nonGenericStruct struct {
	p uint64
}

type IntMap[T any] map[uint64]T

func identity[A any, B any](a A, b B) (A, B) { // ERROR generic functions not supported
	return a, b
}

func identity2[A any](a A) A {
	return a
}

func testGenericStructs() bool {
	var intMap IntMap[uint64]
	intMap = make(IntMap[uint64])
	intMap[1] = 2
	c := genericStruct2[uint64]{
		g: 2,
	}
	u := genericStruct[string, uint64]{
		x: "test",
		y: uint64(7),
	}
	d := identity2[uint64](uint64(5))
	_, d2 := identity("test", uint64(5))
	g := identity[string, uint64]
	_, b := g("test", uint64(3))
	h := nonGenericStruct{
		p: uint64(3),
	}
	return d+d2+c.g+u.y+b+h.p+intMap[1] == 27
}
