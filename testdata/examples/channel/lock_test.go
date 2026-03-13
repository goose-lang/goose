package chan_spec_raw_examples

import (
	"sync"
	"testing"
	"time"
)

func TestLockWithDeadline_ImmediatePastDeadlineFails(t *testing.T) {
	l := NewLock()
	if ok := l.LockWithDeadline(time.Now().Add(-1 * time.Millisecond)); ok {
		t.Fatalf("LockWithDeadline(past) = true; want false")
	}
}

func TestLockWithDeadline_SucceedsWhenFree(t *testing.T) {
	l := NewLock()
	if ok := l.LockWithDeadline(time.Now().Add(200 * time.Millisecond)); !ok {
		t.Fatalf("LockWithDeadline(free) = false; want true")
	}
	l.Unlock()
}

func TestLockWithDeadline_TimesOutWhenHeld(t *testing.T) {
	l := NewLock()
	l.Lock()
	defer l.Unlock()

	start := time.Now()
	ok := l.LockWithDeadline(time.Now().Add(50 * time.Millisecond))
	elapsed := time.Since(start)

	if ok {
		t.Fatalf("LockWithDeadline() = true while held; want false")
	}
	// Fuzzy: timer/scheduler jitter.
	if elapsed < 20*time.Millisecond {
		t.Fatalf("LockWithDeadline returned too fast: %v", elapsed)
	}
	if elapsed > 400*time.Millisecond {
		t.Fatalf("LockWithDeadline took too long: %v", elapsed)
	}
}

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
