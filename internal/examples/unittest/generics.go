package unittest

func genericId[T any](x T) T {
	return x
}

func useGenericAtConcrete(x uint64) uint64 {
	// TODO: the translation looks right but we actually need to take and pass
	//  the type u64T to genericId, for more complex examples like the below
	return genericId(x)
}

func useGenericAtTypeParam[T any](x T) T {
	return genericId(x)
}

// explicitly pass a type parameter
/*
func callWithType[T any](x T) T {
	return genericId[T](x)
}
*/

func loadGeneric[T any](x *T) T {
	// TODO: this is translated incorrectly
	//  (the Gallina definition needs to take a ty argument T,
	//  which is used in the model)
	return *x
}

func allocateGeneric[T any]() *T {
	// TODO: translated incorrectly for the same reason as loadGeneric
	return new(T)
}
