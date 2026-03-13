package chan_spec_raw_examples

import (
	"sync"
	"testing"
	"time"
)

func TestLockWithTimeout_WrapsLockWithDeadline(t *testing.T) {
	l := NewLock()
	l.Lock()
	defer l.Unlock()

	ok := l.LockWithTimeout(30 * time.Millisecond)
	if ok {
		t.Fatalf("LockWithTimeout() = true while held; want false")
	}
}

func BenchmarkLock_Uncontended(b *testing.B) {
	l := NewLock()
	for b.Loop() {
		l.Lock()
		l.Unlock()
	}
}

func BenchmarkLock_Contended(b *testing.B) {
	l := NewLock()
	b.SetParallelism(10)
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			l.Lock()
			l.Unlock()
		}
	})
}

func BenchmarkMutex_Uncontended(b *testing.B) {
	var mu sync.Mutex
	for b.Loop() {
		mu.Lock()
		mu.Unlock()
	}
}

func BenchmarkMutex_Contended(b *testing.B) {
	var mu sync.Mutex
	b.SetParallelism(10)
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			mu.Lock()
			mu.Unlock()
		}
	})
}
