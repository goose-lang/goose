package unittest

// Should be able to detect even if in nested scopes.
func recur1() {
	if true {
		recur1()
	}
}

type recurStruct1 struct{}

func (s *recurStruct1) recur2() {
	s.recur2()
}

type recurStruct2 struct {
	lam func()
}

func (s *recurStruct2) recur3() {
	s.lam = func() {
		s.lam()
	}
	s.lam()
}
