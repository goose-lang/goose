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
