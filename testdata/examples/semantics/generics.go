package semantics

type genericStruct[A any, B any] struct {
	x A
	y B
}

func identity[A any, B any](data genericStruct[A, B]) (A, B) {
	return data.x, data.y
}

func testGenericStructs() bool {
	z := genericStruct[uint64, uint64]{
		x: uint64(7),
		y: uint64(8),
	}

	f := identity[uint64, uint64]

	x, y := f(z)

	return x == z.x && y == z.y
}
