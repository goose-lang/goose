package chan_spec_raw_examples

import (
	"time"

	"github.com/goose-lang/goose/model/channel"
)

// The examples in this file are written to use channel model code directly. After channel
// translation is implemented these will be removed, but using this for now as a means to work on
// verifying examples.

func HelloWorldAsyncX() *channel.Channel[string] {
	ch := channel.NewChannel[string](1)
	go func() {
		ch.Send(sys_hello_world())
	}()
	return ch
}

func HelloWorldSyncX() string {
	return HelloWorldAsyncX().ReceiveDiscardOk()
}

// Simulates the error/done channel components of Context
func HelloWorldCancellableX(done *channel.Channel[struct{}], err *string) string {
	future := HelloWorldAsyncX()
	selected_case, resolved, _, _ := channel.BlockingSelect2(
		future, channel.SelectRecv, "",
		done, channel.SelectRecv, struct{}{})
	if selected_case == 0 {
		return resolved
	} else { // selected_case == 1
		return *err
	}
}

// Uses cancellation as a timeout mechanism.
func HelloWorldWithTimeoutX() string {
	done := channel.NewChannel[struct{}](0)
	errMsg := ""
	// Timeout goroutine updates errMsg only when timeout hits
	go func() {
		time.Sleep(10 * time.Millisecond) // short timeout to trigger cancellation
		errMsg = "operation timed out"    // update error message
		done.Close()                      // signal cancellation
	}()
	return HelloWorldCancellableX(done, &errMsg)
}

// prog3 from Actris 2.0 intro: https://arxiv.org/pdf/2010.15030
func DSPExampleX() int {
	c := channel.NewChannel[any](0)
	signal := channel.NewChannel[any](0)
	go func() {
		ptr := c.ReceiveDiscardOk().(*int) // receive pointer ℓ
		*ptr = *ptr + 2                    // update *ℓ to *ℓ + 2
		signal.Send(struct{}{})            // send signal ()
	}()
	val := 40
	ptr := &val               // create reference ℓ := ref 40
	c.Send(ptr)               // send pointer ℓ
	signal.ReceiveDiscardOk() // receive signal
	return *ptr               // dereference to get 42
}

// https://go.dev/tour/concurrency/4
func fibonacciX(n int, c *channel.Channel[int]) {
	x, y := 0, 1
	for i := 0; i < n; i++ {
		c.Send(x)
		x, y = y, x+y
	}
	c.Close()
}

func fib_consumerX() []int {
	c := channel.NewChannel[int](10)
	go fibonacciX(10, c)
	results := []int{}
	for {
		i, ok := c.Receive()
		if !ok {
			break
		}
		results = append(results, i)
	}
	return results
}

// Show that it isn't possible to have 2 nonblocking ops that match.
func select_nb_no_panicX() {
	ch := channel.NewChannel[struct{}](0)
	go func() {
		selected, _, _ := channel.NonBlockingSelect1(ch, channel.SelectRecv, struct{}{})
		if selected {
			panic("bad")
		}
	}()
	selected, _, _ := channel.NonBlockingSelect1(ch, channel.SelectSend, struct{}{})
	if selected {
		panic("bad")
	}
}

// Show that a guaranteed to be ready case makes default impossible
func select_ready_case_no_panicX() {
	ch := channel.NewChannel[struct{}](0)
	ch.Close()
	selected, _, _ := channel.NonBlockingSelect1(ch, channel.SelectRecv, struct{}{})
	if !selected {
		// Shouldn't be possible, the channel is closed so receive should be ready
		panic("Shouldn't be possible!")
	}
}

// Various tests that should panic when failing, which also means verifying { True } e { True } is
// sufficient since panic can't be verified.
func TestHelloWorldSyncX() {
	result := HelloWorldSync()
	if result != "Hello, World!" {
		panic("incorrect output")
	}
}

func TestHelloWorldWithTimeoutX() {
	result := HelloWorldWithTimeout()
	if result != "operation timed out" && result != "Hello, World!" {
		panic("incorrect output")
	}
}

func TestDSPExampleX() {
	result := DSPExample()
	if result != 42 {
		panic("incorrect output")
	}
}

func TestFibConsumerX() {
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

func TestSelectNbNoPanicX() {
	select_nb_no_panic()
}

func TestSelectReadyCaseNoPanicX() {
	select_ready_case_no_panic()
}

// The example below is a minimal use of the
// https://go.dev/doc/effective_go#leaky_buffer pattern

func clientX(input []string, freeList *channel.Channel[[]byte], serverChan *channel.Channel[[]byte]) {
	for _, letter := range input {
		var b []byte
		// Non-blocking receive from freeList using Select1(case, false).
		selected, v, _ := channel.NonBlockingSelect1[[]byte](freeList, channel.SelectRecv, []byte{0})
		if selected {
			// Selected: reuse buffer from pool.
			b = v
		} else { // sel == -1 ⇒ not selected
			// Allocate a new minimal buffer.
			b = []byte{0}
		}
		load(&b, letter)   // Put one letter into the buffer.
		serverChan.Send(b) // Send to server (blocks for unbuffered).
	}
	// Signal no more work.
	serverChan.Close()
}

func serverX(output *string, freeList *channel.Channel[[]byte], serverChan *channel.Channel[[]byte], join *channel.Channel[struct{}]) {
	for {

		// Blocking receive from serverChan.
		b, ok := serverChan.Receive()

		// If channel is closed and drained, exit.
		if !ok {
			// Tell main we're done.
			join.Send(struct{}{})
			return
		}

		process(&b, output)

		// Non-blocking return of buffer to freeList; drop if pool full.
		channel.NonBlockingSelect1(freeList, channel.SelectSend, b)

	}
}

func LeakyBufferPipelineX() {
	freeList := channel.NewChannel[[]byte](0) // buffer pool
	serverChan := channel.NewChannel[[]byte](0)
	join := channel.NewChannel[struct{}](0)

	output := ""

	go serverX(&output, freeList, serverChan, join)
	clientX([]string{"h", "e", "l", "l", "o", ",", " ", "w", "o", "r", "l", "d"}, freeList, serverChan)
	// Wait for processing to finish
	join.Receive()

	// At this point, server finished because client closed serverChan.
	if output != "HELLO, WORLD" {
		panic("incorrect output")
	}
}
