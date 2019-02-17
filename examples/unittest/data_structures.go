package unittest

import "github.com/tchajed/goose/machine/filesys"

func UseSlice() {
	s := make([]byte, 1)
	s1 := append(s, s...)
	filesys.AtomicCreate("file", s1)
}

func UseMap() {
	m := make(map[uint64][]byte)
	m[1] = nil
	x, ok := m[2]
	if ok {
		return
	}
	m[3] = x
}

func UsePtr() {
	p := new(uint64)
	*p = 1
	x := *p
	*p = x
}
