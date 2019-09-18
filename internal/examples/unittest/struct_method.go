package unittest

type C struct {
	x uint64
	y uint64
}

func (c C) Add(z uint64) uint64 {
	return c.x + c.y + z
}

func UseAdd() uint64 {
	c := C{x: 2, y: 3}
	r := c.Add(4)
	return r
}

func UseAddWithLiteral() uint64 {
	r := C{x: 2, y: 3}.Add(4)
	return r
}
