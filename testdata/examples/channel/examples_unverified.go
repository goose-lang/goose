package chan_spec_raw_examples

import "time"

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
