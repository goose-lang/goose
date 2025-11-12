package chan_spec_raw_examples

import (
	"strings"
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

// Show that a guaranteed to be ready case makes default impossible
func select_ready_case_no_panic() {
	ch := make(chan struct{})
	close(ch)
	select {
	case <-ch:
		// Channel was closed, we should be entering this block
	default:
		// Shouldn't be possible, the other case is made ready before the select
		panic("Shouldn't be possible!")
	}
}

// Various tests that should panic when failing, which also means verifying { True } e { True } is
// sufficient since panic can't be verified.
func TestHelloWorldSync() {
	result := HelloWorldSync()
	if result != "Hello, World!" {
		panic("incorrect output")
	}
}

func TestHelloWorldWithTimeout() {
	result := HelloWorldWithTimeout()
	if result != "operation timed out" && result != "Hello, World!" {
		panic("incorrect output")
	}
}

func TestDSPExample() {
	result := DSPExample()
	if result != 42 {
		panic("incorrect output")
	}
}

func TestFibConsumer() {
	result := fib_consumer()
	expected := []int{0, 1, 1, 2, 3, 5, 8, 13, 21, 34}

	if len(result) != len(expected) {
		panic("incorrect output")
	}

	for i := range expected {
		if result[i] != expected[i] {
			panic("incorrect output")
		}
	}
}

func TestSelectNbNoPanic() {
	iterations := 10000
	for i := 0; i < iterations; i++ {
		select_nb_no_panic()
		// Small sleep to let the goroutine finish
		time.Sleep(1 * time.Microsecond)
	}
}

func TestSelectReadyCaseNoPanic() {
	iterations := 10000
	for i := 0; i < iterations; i++ {
		select_ready_case_no_panic()
	}
}

// The example below is a minimal use of the
// https://go.dev/doc/effective_go#leaky_buffer pattern

// load writes the next letter into the buffer.
func load(b *[]byte, letter string) {
	*b = []byte(letter)
}

// process consumes the buffer and appends it to the output.
func process(b *[]byte, output *string) {
	*output += strings.ToUpper(string(*b))
}

func client(input []string, freeList chan []byte, serverChan chan []byte) {
	for _, letter := range input {
		var b []byte

		// Non-blocking receive from freeList.
		select {
		case b = <-freeList:
			// Reuse buffer from pool.
		default:
			// Allocate a new minimal buffer.
			b = []byte{0}
		}

		load(&b, letter) // Put one letter into the buffer.
		serverChan <- b  // Blocking send to server.
	}

	// Signal no more work.
	close(serverChan)
}

func server(output *string, freeList chan []byte, serverChan chan []byte, done chan struct{}) {
	for {
		// Blocking receive from serverChan.
		b, ok := <-serverChan
		if !ok {
			// Channel closed and drained.
			done <- struct{}{}
			return
		}

		process(&b, output)

		// Non-blocking return of buffer to freeList; drop if pool full.
		select {
		case freeList <- b:
			// Returned to pool.
		default:
			// Pool full; drop buffer.
		}
	}
}

func LeakyBufferPipeline() {
	freeList := make(chan []byte, 5) // buffer pool
	serverChan := make(chan []byte, 0)
	done := make(chan struct{}, 0)

	output := ""

	go server(&output, freeList, serverChan, done)
	client([]string{"h", "e", "l", "l", "o", ",", " ", "w", "o", "r", "l", "d"}, freeList, serverChan)
	<-done

	// At this point, server finished because client closed serverChan.
	if output != "HELLO, WORLD" {
		panic("incorrect output")
	}
}
