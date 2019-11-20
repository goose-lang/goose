package unittest

type TwoInts struct {
	x uint64
	y uint64
}

type S struct {
	a uint64
	b TwoInts
	c bool
}

func NewS() *S {
	return &S{
		a: 2,
		b: TwoInts{x: 1, y: 2},
		c: true,
	}
}

func (s *S) readA() uint64 {
	return s.a
}

func (s *S) readB() TwoInts {
	return s.b
}

func (s S) readBVal() TwoInts {
	return s.b
}

func (s *S) writeB(two TwoInts) {
	s.b = two
}

func (s *S) negateC() {
	s.c = !s.c
}
