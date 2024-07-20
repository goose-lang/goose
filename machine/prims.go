// Package machine is a support library for generic Go primitives.
//
// GooseLang provides models for all of these operations.
package machine

import (
	"encoding/binary"
	"fmt"
	"math/rand"
	"os"
	"sync"
	"time"

	"github.com/goose-lang/primitive"
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
// a procedure.
func Linearize() {}

// Assume lets the proof assume that `c` is true.
// *Use with care*, assumptions are trusted and should be justified!
// Note that these are *runtime-checked* assumptions, i.e., the worst-case here
// is having the program panic in unexpected ways.
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

// Stop the program with the given exit code.
func Exit(n uint64) {
	os.Exit(int(n))
}

// WaitTimeout is like cond.Wait(),
// but waits for a maximum time of timeoutMs milliseconds.
//
// Not provided by sync.Cond, so we have to (inefficiently) implement this
// ourselves.
func WaitTimeout(cond *sync.Cond, timeoutMs uint64) {
	primitive.WaitTimeout(cond, timeoutMs)
}

func TimeNow() uint64 {
	return uint64(time.Now().UnixNano())
}

func Sleep(ns uint64) {
	time.Sleep(time.Duration(ns) * time.Nanosecond)
}

func MapClear[M ~map[K]V, K comparable, V any](m M) {
	for k := range m {
		delete(m, k)
	}
}
