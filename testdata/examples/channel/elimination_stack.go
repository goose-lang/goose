package chan_spec_raw_examples

import (
	"sync"
	"time"
)

// LockedStack is a simple mutex-protected LIFO stack.
type LockedStack struct {
	mu    sync.Mutex
	stack []string
}

func NewLockedStack() *LockedStack {
	return &LockedStack{stack: make([]string, 0)}
}

func (s *LockedStack) Push(value string) {
	s.mu.Lock()
	s.stack = append(s.stack, value)
	s.mu.Unlock()
}

func (s *LockedStack) Pop() (string, bool) {
	s.mu.Lock()
	if len(s.stack) == 0 {
		s.mu.Unlock()
		return "", false
	}
	last := len(s.stack) - 1
	v := s.stack[last]
	s.stack = s.stack[:last]
	s.mu.Unlock()
	return v, true
}

// after returns a channel that closes after d (emulates time.After).
func after(d time.Duration) <-chan struct{} {
	ch := make(chan struct{})
	go func() {
		time.Sleep(d)
		close(ch)
	}()
	return ch
}

// EliminationStack composes a single-slot exchanger over a LockedStack.
type EliminationStack struct {
	base      *LockedStack
	exchanger chan string // unbuffered: rendezvous
	timeout   time.Duration
}

// NewEliminationStack constructs a new elimination stack
// using a fresh LockedStack and a small default timeout.
func NewEliminationStack() *EliminationStack {
	return &EliminationStack{
		base:      NewLockedStack(),
		exchanger: make(chan string),
		timeout:   10 * time.Microsecond,
	}
}

// Push first tries one-shot elimination; on timeout, falls back to the locked stack.
func (s *EliminationStack) Push(value string) {
	t := after(s.timeout)
	select {
	case s.exchanger <- value:
		// Eliminated with a concurrent Pop.
		return
	case <-t:
		// Timeout; use central stack.
	}
	s.base.Push(value)
}

// Pop first tries one-shot elimination; on timeout, falls back to the locked stack.
func (s *EliminationStack) Pop() (string, bool) {
	t := after(s.timeout)
	select {
	case v := <-s.exchanger:
		// Eliminated with a concurrent Push.
		return v, true
	case <-t:
		// Timeout; use central stack.
	}
	return s.base.Pop()
}
