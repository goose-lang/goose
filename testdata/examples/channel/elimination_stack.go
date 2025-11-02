package chan_spec_raw_examples

import (
	"sync"
	"time"
)

type EliminationStack struct {
	stack     []string
	mu        sync.Mutex
	exchanger chan string
}

func NewEliminationStack() *EliminationStack {
	return &EliminationStack{
		stack:     make([]string, 0),
		exchanger: make(chan string),
	}
}

func (s *EliminationStack) Push(value string) {
	// Try single-slot elimination once.
	select {
	case s.exchanger <- value:
		return
	case <-time.After(10 * time.Microsecond):
		// fall through to central stack
	}
	// Central stack fallback
	s.mu.Lock()
	s.stack = append(s.stack, value)
	s.mu.Unlock()
}

func (s *EliminationStack) Pop() (string, bool) {
	// Try single-slot elimination once.
	select {
	case v := <-s.exchanger:
		return v, true // eliminated with a concurrent Push
	case <-time.After(10 * time.Microsecond):
		// fall through to central stack
	}
	// Central stack fallback
	s.mu.Lock()
	if len(s.stack) == 0 {
		s.mu.Unlock()
		return "", false
	}
	v := s.stack[len(s.stack)-1]
	s.stack = s.stack[:len(s.stack)-1]
	s.mu.Unlock()
	return v, true
}
