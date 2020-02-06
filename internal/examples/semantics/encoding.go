package semantics

import "github.com/tchajed/goose/machine"

// helpers
type Enc struct {
	p []byte
}

func (e *Enc) consume(n uint64) []byte {
	b := e.p[:n]
	e.p = e.p[n:]
	return b
}

type Dec struct {
	p []byte
}

func (d *Dec) consume(n uint64) []byte {
	b := d.p[:n]
	d.p = d.p[n:]
	return b
}

func roundtripEncDec32(x uint32) uint32 {
	r := make([]byte, 4)
	e := &Enc{p: r}
	d := &Dec{p: r}
	machine.UInt32Put(e.consume(4), x)
	return machine.UInt32Get(d.consume(4))
}

func roundtripEncDec64(x uint64) uint64 {
	r := make([]byte, 8)
	e := &Enc{p: r}
	d := &Dec{p: r}
	machine.UInt64Put(e.consume(8), x)
	return machine.UInt64Get(d.consume(8))
}

// tests
func testEncDec32Simple() bool {
	var ok = true
	ok = ok && (roundtripEncDec32(0) == 0)
	ok = ok && (roundtripEncDec32(1) == 1)
	ok = ok && (roundtripEncDec32(1231234) == 1231234)
	return ok
}

func testEncDec32() bool {
	var ok = true
	ok = ok && (roundtripEncDec32(0xCCBB00AA) == 0xCCBB00AA)
	ok = ok && (roundtripEncDec32(1<<20) == 1<<20)
	ok = ok && (roundtripEncDec32(1<<18) == 1<<18)
	ok = ok && (roundtripEncDec32(1<<10) == 1<<10)
	ok = ok && (roundtripEncDec32(1<<0) == 1<<0)
	ok = ok && (roundtripEncDec32(1<<32-1) == 1<<32-1)
	return ok
}

func testEncDec64Simple() bool {
	var ok = true
	ok = ok && (roundtripEncDec64(0) == 0)
	ok = ok && (roundtripEncDec64(1) == 1)
	ok = ok && (roundtripEncDec64(1231234) == 1231234)
	return ok
}

func testEncDec64() bool {
	var ok = true
	ok = ok && (roundtripEncDec64(0xDD00CC00BB00AA) == 0xDD00CC00BB00AA)
	ok = ok && (roundtripEncDec64(1<<63) == 1<<63)
	ok = ok && (roundtripEncDec64(1<<47) == 1<<47)
	ok = ok && (roundtripEncDec64(1<<20) == 1<<20)
	ok = ok && (roundtripEncDec64(1<<18) == 1<<18)
	ok = ok && (roundtripEncDec64(1<<10) == 1<<10)
	ok = ok && (roundtripEncDec64(1<<0) == 1<<0)
	ok = ok && (roundtripEncDec64(1<<64-1) == 1<<64-1)
	return ok
}
