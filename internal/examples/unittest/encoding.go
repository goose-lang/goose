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

func EncDec32(x uint32) bool {
	r := make([]byte, 4)
	e := &Enc{p: r}
	d := &Dec{p: r}
	e.UInt32(x)
	return x == d.UInt32()
}

func EncDec64(x uint64) bool {
	r := make([]byte, 8)
	e := &Enc{p: r}
	d := &Dec{p: r}
	e.UInt64(x)
	return x == d.UInt64()
}
