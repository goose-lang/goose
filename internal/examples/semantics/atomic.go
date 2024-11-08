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
