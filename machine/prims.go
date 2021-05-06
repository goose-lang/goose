// Package machine is a support library for operations on integers.
//
// Goose code can use these additional functions. They have corresponding
// primitives and a model in the Goose `Heap.v` model of Go's built-in heap data
// structures, under the `Data` module.
package machine

import (
	"encoding/binary"
	"fmt"
	"math/rand"
	"sync"
	"time"
)

// UInt64Get converts the first 8 bytes of p to a uint64.
//
// Requires p be at least 8 bytes long.
//
// Happens to decode in little-endian byte order, but this is only relevant as
// far as the relationship between UInt64Get and UInt64Encode.
func UInt64Get(p []byte) uint64 {
	return binary.LittleEndian.Uint64(p)
}

// 32-bit version
func UInt32Get(p []byte) uint32 {
	return binary.LittleEndian.Uint32(p)
}

// UInt64Put stores n to the first 8 bytes of p
//
// Requires p to be at least 8 bytes long.
//
// Uses little-endian byte order, but this is only relevant in that it's the
// inverse of UInt64Get.
func UInt64Put(p []byte, n uint64) {
	binary.LittleEndian.PutUint64(p, n)
}

// 32-bit version
func UInt32Put(p []byte, n uint32) {
	binary.LittleEndian.PutUint32(p, n)
}

// RandomUint64 returns a random uint64 using the global seed.
func RandomUint64() uint64 {
	return rand.Uint64()
}

// UInt64ToString formats a number as a string.
//
// Assumed to be pure and injective in the Coq model.
func UInt64ToString(x uint64) string {
	return fmt.Sprintf("%d", x)
}

// Linearize does nothing.
//
// Translates to an atomic step that supports opening invariants conveniently for
// the sake of executing a simulation fancy update at the linearization point of
// a procedure..
func Linearize() {}

// Assume lets the proof assume that `c` is true.
// *Use with care*, assumptions are trusted and should be justified!
//
// The Go implementation will panic (quit the process in a controlled manner) if
// `c` is not true. (Not to be confused with GooseLang `Panic` which is UB.)
// In GooseLang, it will loop infinitely.
func Assume(c bool) {
	if !c {
		panic("Assume condition violated")
	}
}

// Assert induces a proof obligation that `c` is true.
//
// The Go implementation will panic (quit the process in a controlled manner) if
// `c` is not true. In GooseLang, it will make the machine stuck, i.e., cause UB.
func Assert(c bool) {
	if !c {
		panic("Assert condition violated")
	}
}

// Go's "sync" is very limited, so we have to (inefficiently) implement this ourselves.
// Timeout is in milliseconds.
func WaitTimeout(cond *sync.Cond, timeout_ms uint64) {
	done := make(chan struct{})
	go func() {
		cond.Wait()
		cond.L.Unlock()
		close(done)
	}()
	select {
	case <-time.After(time.Duration(timeout_ms * 1000 * 1000)): // convert to nanoseconds
		// timed out
		cond.L.Lock()
		return
	case <-done:
		// Wait returned
		cond.L.Lock()
		return
	}
}
