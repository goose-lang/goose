package semantics

type pair struct {
	a uint64
	b uint64
}

func newGeneric[T any]() *T {
	return new(T)
}

func storeAndLoadGeneric[T any](t *T, v T) T {
	*t = v
	return *t
}

func testGenerics() bool {
	x := newGeneric[pair]()

	res := storeAndLoadGeneric(x, pair{a: 10, b: 37})
	return res.a == 10 && res.b == 37
}
