package unittest

type C struct {
	x uint64
	y uint64
}

func (c C) Add(z uint64) uint64 {
	return c.x + c.y + z
}
