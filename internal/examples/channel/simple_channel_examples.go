package channel_spec_test

// These are basic Go channel examples that demonstrate and test
//  the patterns and anti-patterns we are looking to specify/prevent.
// These indicate failure by panicking so that they cannot be proven
// unless they don't panic

// Example 1: Simple goroutine sending a string, check basic message passing without
// synchronization
func SendMessage() {
	// Create an unbuffered channel for the message
	messageChan := make(chan string)

	// Start a goroutine to send the message
	go func() {
		messageChan <- "hello world"
	}()

	// Receive the message
	message := <-messageChan

	// Verification check
	if message != "hello world" {
		panic("Did not receive expected message")
	}
}

// Example 2: Join goroutine with receive on unbuffered channel
func JoinWithReceive() {
	// Create string pointer with initial empty value
	var message *string = new(string)

	// Create unbuffered channel for synchronization
	done := make(chan uint64)

	// Launch goroutine
	go func() {
		// Set the message
		*message = "hello world"

		// Signal completion
		done <- 0
	}()

	// Join goroutine by receiving from channel
	<-done

	// Verify message was set correctly
	if *message != "hello world" {
		panic("Message was not set correctly")
	}
}

// Example 3: Join goroutine with send on unbuffered channel
func JoinWithSend() {
	// Create string pointer with initial empty value
	var message *string = new(string)

	// Create unbuffered channel for synchronization
	done := make(chan uint64)

	// Launch goroutine
	go func() {
		// Set the message
		*message = "hello world"

		// Wait for acknowledgment
		<-done
	}()

	// Join goroutine by sending to channel
	done <- 0

	// Verify message was set correctly
	if *message != "hello world" {
		panic("Message was not set correctly")
	}
}

// Example 4: Map stage pipeline that doubles a list of 3 numbers
/* TODO: Need to support translation of channel range for
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
*/

// Example 5: Parallel double values with buffered channel
/* TODO: Need to support translation of channel range for
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
*/

// Example 6: Broadcast notification with close. This is testing a case where
// we transfer disjoint ownership to different threads in a single broadcast
func BroadcastNotification() {
	// Create notification channel
	notifyCh := make(chan uint64)

	// Create done channels for synchronization
	done1 := make(chan uint64)
	done2 := make(chan uint64)
	done3 := make(chan uint64)

	// Create a list of 3 strings, initially empty
	var results []string
	results = append(results, "")
	results = append(results, "")
	results = append(results, "")

	// Start 3 goroutines
	go func() {
		<-notifyCh // Wait for notification
		if results[0] != "thread1" {
			panic("Thread 1 received incorrect value")
		}
		done1 <- 0
	}()

	go func() {
		<-notifyCh // Wait for notification
		if results[1] != "thread2" {
			panic("Thread 2 received incorrect value")
		}
		done2 <- 0
	}()

	go func() {
		<-notifyCh // Wait for notification
		if results[2] != "thread3" {
			panic("Thread 3 received incorrect value")
		}
		done3 <- 0
	}()

	// Set values in the list
	results[0] = "thread1"
	results[1] = "thread2"
	results[2] = "thread3"

	// Close channel to notify all goroutines
	close(notifyCh)

	// Wait for all goroutines to complete
	<-done1
	<-done2
	<-done3
}

// Example 7: Join sending goroutine before closing a buffered channel.
// This should demonstrate the spec's ability to prevent closing on a channel
// without joining all the senders.
func CoordinatedChannelClose() {
	// Create a buffered channel
	bufCh := make(chan uint64, 2)

	// Create a synchronization channel
	syncCh := make(chan uint64)

	// Start goroutine that sends to buffered channel
	go func() {
		bufCh <- 42

		// Signal completion
		syncCh <- 0
	}()

	// Send from main function
	bufCh <- 84

	// Wait for goroutine to complete sending
	<-syncCh

	// Now safe to close the channel
	close(bufCh)

	// Read all values
	val1 := <-bufCh
	val2 := <-bufCh

	// Check that we got both values
	if !((val1 == 42 && val2 == 84) || (val1 == 84 && val2 == 42)) {
		panic("Did not receive both expected values")
	}
}

// Example 8: Select between two immediately selectable channels. This tests subtle
// behavior of select: We shouldn't be selecting the same closed receive case
// twice which we can prevent by setting the channel to nil. We shouldn't select the
// buffered case twice since we only send 1 value, though this will be harder to specify.
/* TODO: Need to support translation of channel select
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
*/
