package unittest

func genericId[T any](x T) T {
	return x
}

func useGenericImplicitly(x uint64) uint64 {
	return genericId(x)
}

func useGenericAtTypeParam[T any](x T) T {
	return genericId(x)
}

func useGenericExplicitly[T any](x T) T {
	return genericId[T](x)
}

func loadGeneric[T any](x *T) T {
	return *x
}

func allocateGeneric[T any]() *T {
	return new(T)
}

func multipleTypes[T, V any](x T, v V) V {
	return v
}

func callWithMultipleTypes() {
	multipleTypes[uint64, bool](3, true)
}

func callWithMultipleTypesImplicit() {
	multipleTypes(false, uint64(2))
}

func callWithPartialInstantiation() {
	multipleTypes[bool](false, uint64(2))
}

// type Box[T any] struct {
// v T
// }
