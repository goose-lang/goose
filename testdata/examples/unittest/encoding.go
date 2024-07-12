package unittest

import "github.com/tchajed/goose/machine"

type Enc struct {
	p []byte
}

func (e *Enc) consume(n uint64) []byte {
	b := e.p[:n]
	e.p = e.p[n:]
	return b
}

func (e *Enc) UInt64(x uint64) {
	machine.UInt64Put(e.consume(8), x)
}

func (e *Enc) UInt32(x uint32) {
	machine.UInt32Put(e.consume(4), x)
}

type Dec struct {
	p []byte
}

func (d *Dec) consume(n uint64) []byte {
	b := d.p[:n]
	d.p = d.p[n:]
	return b
}

func (d *Dec) UInt64() uint64 {
	return machine.UInt64Get(d.consume(8))
}

func (d *Dec) UInt32() uint32 {
	return machine.UInt32Get(d.consume(4))
}
