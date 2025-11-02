package chan_spec_raw_examples

import (
	"fmt"
	"strconv"
	"sync"
	"testing"
)

func TestBasicLIFO(t *testing.T) {
	s := NewEliminationStack()

	s.Push("1")
	s.Push("2")
	s.Push("3")

	if v, ok := s.Pop(); !ok || v != "3" {
		panic(fmt.Sprintf("Expected 3, got %v", v))
	}
	if v, ok := s.Pop(); !ok || v != "2" {
		panic(fmt.Sprintf("Expected 2, got %v", v))
	}
	if v, ok := s.Pop(); !ok || v != "1" {
		panic(fmt.Sprintf("Expected 1, got %v", v))
	}
	if _, ok := s.Pop(); ok {
		panic("Expected empty stack")
	}
}

func TestConcurrentPushPop(t *testing.T) {
	s := NewEliminationStack()

	const ops = 100
	var wg sync.WaitGroup
	wg.Add(2)

	// Pusher
	go func() {
		defer wg.Done()
		for i := 1; i <= ops; i++ {
			s.Push(strconv.Itoa(i))
		}
	}()

	// Popper
	popped := 0
	var mu sync.Mutex
	go func() {
		defer wg.Done()
		for i := 0; i < ops; i++ {
			if _, ok := s.Pop(); ok {
				mu.Lock()
				popped++
				mu.Unlock()
			}
		}
	}()

	wg.Wait()

	// All items should be accounted for (popped + remaining)
	s.mu.Lock()
	remaining := len(s.stack)
	s.mu.Unlock()

	if popped+remaining != ops {
		panic(fmt.Sprintf("Lost items: pushed=%d, popped=%d, remaining=%d",
			ops, popped, remaining))
	}
}

func TestEliminationStack(t *testing.T) {
	s := NewEliminationStack()

	const pairs = 100
	var wg sync.WaitGroup
	wg.Add(pairs * 2)

	start := make(chan struct{})

	// Launch pairs simultaneously
	for i := 1; i <= pairs; i++ {
		go func(v int) {
			defer wg.Done()
			<-start
			s.Push(strconv.Itoa(v))
		}(i)

		go func() {
			defer wg.Done()
			<-start
			s.Pop()
		}()
	}

	close(start)
	wg.Wait()

	// Just verify no panics occurred and stack is in valid state
	s.mu.Lock()
	remaining := len(s.stack)
	s.mu.Unlock()

	if remaining < 0 || remaining > pairs {
		panic(fmt.Sprintf("Invalid remaining count: %d", remaining))
	}
}

func TestHighContention(t *testing.T) {
	s := NewEliminationStack()

	var wg sync.WaitGroup
	wg.Add(4)

	for i := 0; i < 2; i++ {
		go func(id int) {
			defer wg.Done()
			for j := 0; j < 50; j++ {
				s.Push(strconv.Itoa(id*100 + j))
			}
		}(i)

		go func() {
			defer wg.Done()
			for j := 0; j < 50; j++ {
				s.Pop()
			}
		}()
	}

	wg.Wait()

	// Verify stack is in valid state
	s.mu.Lock()
	remaining := len(s.stack)
	s.mu.Unlock()

	if remaining < 0 || remaining > 100 {
		panic(fmt.Sprintf("Invalid stack state: %d items", remaining))
	}
}
