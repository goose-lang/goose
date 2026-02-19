package chan_spec_raw_examples

import (
	"time"
)

// Fake syscall for demonstration.
func sys_hello_world() string {
	return "Hello, World!"
}

func HelloWorldAsync() chan string {
	ch := make(chan string, 1)
	go func() {
		ch <- sys_hello_world()
	}()
	return ch
}

func HelloWorldSync() string {
	return <-HelloWorldAsync()
}

// Simulates the error/done channel components of Context
func HelloWorldCancellable(done chan struct{}, err *string) string {
	future := HelloWorldAsync()
	select {
	case resolved := <-future:
		return resolved
	case <-done:
		return *err
	}
}

// Uses cancellation as a timeout mechanism.
func HelloWorldWithTimeout() string {
	done := make(chan struct{})
	errMsg := ""

	// Timeout goroutine updates errMsg only when timeout hits
	go func() {
		time.Sleep(10 * time.Millisecond) // short timeout to trigger cancellation
		errMsg = "operation timed out"    // update error message
		close(done)                       // signal cancellation
	}()

	return HelloWorldCancellable(done, &errMsg)
}

// prog3 from Actris 2.0 intro: https://arxiv.org/pdf/2010.15030
func DSPExample() int {
	c := make(chan any)
	signal := make(chan any)

	go func() {
		ptr := (<-c).(*int)  // receive pointer ℓ
		*ptr = *ptr + 2      // update *ℓ to *ℓ + 2
		signal <- struct{}{} // send signal ()
	}()

	val := 40
	ptr := &val // create reference ℓ := ref 40
	c <- ptr    // send pointer ℓ
	<-signal    // receive signal
	return *ptr // dereference to get 42
}

// https://go.dev/tour/concurrency/4
func fibonacci(n int, c chan int) {
	x, y := 0, 1
	for i := 0; i < n; i++ {
		c <- x
		x, y = y, x+y
	}
	close(c)
}

func fib_consumer() []int {
	c := make(chan int, 10)
	go fibonacci(cap(c), c)

	results := []int{}
	for i := range c {
		results = append(results, i)
	}
	return results
}

func simple_join() string {
	ch := make(chan struct{}, 1)
	var message string

	go func() {
		message = "Hello, World!"
		ch <- struct{}{}
	}()

	<-ch // Wait for goroutine to finish
	return message
}

func simple_multi_join() string {
	ch := make(chan struct{}, 2)
	var hello, world string

	go func() {
		hello = "Hello"
		ch <- struct{}{}
	}()
	go func() {
		world = "World"
		ch <- struct{}{}
	}()
	// Wait for both goroutines
	<-ch
	<-ch
	return hello + " " + world
}

// Show that it isn't possible to have 2 nonblocking ops that match.
func select_nb_no_panic() {
	ch := make(chan struct{})
	go func() {
		select {
		case <-ch:
			panic("bad")
		default:
		}
	}()

	select {
	case ch <- struct{}{}:
		panic("bad")
	default:
	}
}

func select_no_double_close() {
	x := make(chan int)
	close(x)
	select {
	case <-x:
	default:
		close(x)
	}
}

// Show that a nonblocking select does not take a send case
// when the buffered channel is already full.
func select_nb_full_buffer_no_panic() {
	// 1. Buffered channel of size 1
	ch := make(chan int, 1)

	// 2. Fill the buffer
	ch <- 0

	// 3. Nonblocking select:
	//    the send case would panic,
	//    so it must NOT be taken.
	select {
	case ch <- 0:
		panic("unreachable")
	default:
		// benign: correct behavior
	}
}

// Unverifiable: Panic is irreducible
func select_nb_buffer_space_panic() {
	// Create a buffered channel with capacity 1
	ch := make(chan int, 1)

	// Nonblocking select:
	// the send case is enabled and may be chosen.
	select {
	case ch <- 0:
		// This panic is reachable
		panic("bad")
	default:
	}
}

// Blocking select: vacuously verifiable due to deadlock
func select_nb_buffer_space_deadlock() {
	// Create a buffered channel with capacity 1
	ch := make(chan int, 1)

	// First send fills the buffer
	ch <- 0

	// Blocks indefinitely on send.
	select {
	case ch <- 0:
		// This code is unreachable
		panic("unreachable")
	}
}

func exchangePointer() {
	x := 0
	y := 0

	ch := make(chan struct{})
	go func() {
		x = 1
		ch <- struct{}{}
		if y != 2 {
			panic("bad")
		}
	}()

	y = 2
	<-ch
	if x != 1 {
		panic("bad")
	}
}

func BroadcastExample() {
	done := make(chan struct{})
	result1 := make(chan uint64)
	result2 := make(chan uint64)

	var sharedValue uint64

	go func() {
		<-done // Wait for broadcast
		val := sharedValue
		result1 <- val * 3
	}()

	go func() {
		<-done // Wait for broadcast
		val := sharedValue
		result2 <- val * 5
	}()

	sharedValue = 2

	// Broadcast that value is ready
	close(done)

	// Read results and assert
	r1 := <-result1
	r2 := <-result2

	if r1 != 6 {
		panic("receiver 1 got wrong value")
	}
	if r2 != 10 {
		panic("receiver 2 got wrong value")
	}
}

func Web(query string) string {
	return query + ".html"
}

func Image(query string) string {
	return query + ".png"
}

func Video(query string) string {
	return query + ".mp4"
}

// https://go.dev/talks/2012/concurrency.slide#46
func Google(query string) []string {
	c := make(chan string, 3)

	go func() { c <- Web(query) }()
	go func() { c <- Image(query) }()
	go func() { c <- Video(query) }()

	results := make([]string, 0, 3)
	for i := 0; i < 3; i++ {
		r := <-c
		results = append(results, r)
	}
	return results
}
