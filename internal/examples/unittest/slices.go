package unittest

func sliceOps() uint64 {
	x := make([]uint64, 10)
	v1 := x[2]
	v2 := x[2:3]
	v3 := x[:3]
	v4 := &x[2]
	return v1 + v2[0] + v3[1] + *v4
}
