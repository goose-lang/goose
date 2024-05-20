package unittest

func recur1(n uint64) uint64 {
	// Test translation even from within nested scopes.
	var out uint64
	for i := uint64(0); i < 1; i++ {
		if i == 0 {
			// TODO: gets translated as `recur1`, not `"recur1"`.
			out = recur1(n - 1)
			break
		}
	}
	return out
}

type recurStruct1 struct{}

func (s *recurStruct1) recur2(n uint64) uint64 {
	// TODO: needs quotes here.
	return s.recur2(n)
}

func recur3(n uint64) uint64 {
	// TODO: if we support func ptrs in map, what's the delta to
	// supporting them as their own var decl?
	handlers := make(map[uint64]func(uint64) uint64)
	handlers[0] = func(n uint64) uint64 {
		// TODO: Goose doesn't add MapGet when we immediately call func.
		return handlers[0](n)
	}
	return handlers[0](n)
}

type recurStruct2 struct {
	lam func(uint64) uint64
}

func (s *recurStruct2) recur4(n uint64) uint64 {
	s.lam = func(n uint64) uint64 {
		return s.lam(n)
	}
	return s.lam(n)
}
