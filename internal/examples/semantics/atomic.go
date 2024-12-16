package semantics

import "sync/atomic"

func testAtomicLoadStore64() bool {
	var x uint64
	var ok = true
	atomic.StoreUint64(&x, 42)
	y := atomic.LoadUint64(&x)
	ok = ok && y == 42
	atomic.StoreUint64(&x, 1)
	z := atomic.LoadUint64(&x)
	ok = ok && z == 1
	return ok
}

func testAtomicPointers() bool {
	p := &atomic.Pointer[uint64]{}
	var x uint64
	p.Store(&x)
	y := p.Load()
	*y = 1
	var ok = true
	ok = ok && x == 1
	return ok
}
