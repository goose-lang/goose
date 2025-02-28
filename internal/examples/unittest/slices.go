package unittest

type SliceNamed []bool

type SliceAlias = []uint32

func sliceOps() uint64 {
	x := make([]uint64, 10)
	v1 := x[2]
	v2 := x[2:3]
	v3 := x[:3]
	v4 := &x[2]
	return v1 + v2[0] + v3[1] + *v4 + uint64(len(x)) + uint64(cap(x))
}

func makeSingletonSlice(x uint64) []uint64 {
	return []uint64{x}
}

type thing struct {
	x uint64
}

type sliceOfThings struct {
	things []thing
}

func (ts sliceOfThings) getThingRef(i uint64) *thing {
	return &ts.things[i]
}

func makeNamed() SliceNamed {
	return make(SliceNamed, 10)
}

func useAlias() uint32 {
	s := make(SliceAlias, 10)
	s2 := make(SliceAlias, 5)
	copy(s, s2)
	return s[2]
}
