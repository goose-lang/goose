//go:build !goose

package channel_spec_test

// These are more complicated Go channel examples that demonstrate more complex
// patterns and subtle antipatterns. These panic if their properties fail to be
// met so that they cannot be proven without showing they can't panic.

// Example 1: Map stage pipeline that doubles a list of 3 numbers
func DoubleValues() {
	var val1 uint64 = 5
	var val2 uint64 = 10
	var val3 uint64 = 15

	var values []*uint64
	values = append(values, &val1)
	values = append(values, &val2)
	values = append(values, &val3)

	// Create an unbuffered channel for processing
	ch := make(chan *uint64)

	// Start a worker goroutine
	go func() {
		// Process each pointer using range
		for ptr := range ch {
			*ptr = *ptr * 2
		}
	}()

	// Send pointers to the goroutine for processing
	ch <- values[0]
	ch <- values[1]
	ch <- values[2]

	// Close the channel
	close(ch)

	// Check if values were doubled correctly
	if !(val1 == 10 && val2 == 20 && val3 == 30) {
		panic("Values were not doubled correctly")
	}
}

// Example 2: Parallel double values with buffered channel
func DoubleValuesParallel() {
	// Create an array of uint64 pointers with size 3
	var val1 uint64 = 5
	var val2 uint64 = 10
	var val3 uint64 = 15

	var values []*uint64
	values = append(values, &val1)
	values = append(values, &val2)
	values = append(values, &val3)

	// Create a buffered channel for both input and results
	workCh := make(chan *uint64, 3)
	resultCh := make(chan uint64, 3)

	// Start two worker goroutines
	go func() {
		for ptr := range workCh {
			*ptr = *ptr * 2
			resultCh <- *ptr
		}
	}()

	go func() {
		for ptr := range workCh {
			*ptr = *ptr * 2
			resultCh <- *ptr
		}
	}()

	// Send work to the goroutines
	workCh <- values[0]
	workCh <- values[1]
	workCh <- values[2]
	close(workCh)

	// Collect results
	r1 := <-resultCh
	r2 := <-resultCh
	r3 := <-resultCh

	// Verify results - check if we have all expected values
	hasVal1 := (r1 == 10 || r2 == 10 || r3 == 10)
	hasVal2 := (r1 == 20 || r2 == 20 || r3 == 20)
	hasVal3 := (r1 == 30 || r2 == 30 || r3 == 30)

	if !(hasVal1 && hasVal2 && hasVal3) {
		panic("Did not receive all expected values")
	}
}

// Example 3: Select between two immediately selectable channels. This tests subtle
// behavior of select: We shouldn't be selecting the same closed receive case
// twice which we can prevent by setting the channel to nil. We shouldn't select the
// buffered case twice since we only send 1 value, though this will be harder to specify.
func SelectBetweenBufferedAndClosed() {
	// Create a buffered channel with a value and an unbuffered channel
	bufferedCh := make(chan string, 1)
	unbufferedCh := make(chan string)

	// Create counters to track which case was selected
	var firstCaseSelected uint64 = 0
	var secondCaseSelected uint64 = 0

	// Buffer a value
	bufferedCh <- "value"

	// Close the unbuffered channel immediately
	close(unbufferedCh)

	// First select - both cases are immediately selectable
	select {
	case _, ok := <-unbufferedCh:
		firstCaseSelected++
		if !ok {
			// Channel is closed, set to nil to prevent further selection
			unbufferedCh = nil
		}
	case <-bufferedCh:
		secondCaseSelected++
	}

	// Check after first select - exactly one case should be selected
	if !((firstCaseSelected == 1 && secondCaseSelected == 0) ||
		(firstCaseSelected == 0 && secondCaseSelected == 1)) {
		panic("After first select: Expected exactly one case to be selected")
	}

	// Second select - identical to the first one
	select {
	case _, ok := <-unbufferedCh:
		firstCaseSelected++
		if !ok {
			unbufferedCh = nil
		}
	case <-bufferedCh:
		secondCaseSelected++
	}

	// Check after second select - both should be selected exactly once
	if !(firstCaseSelected == 1 && secondCaseSelected == 1) {
		panic("After second select: Expected both cases to be selected exactly once")
	}
}
