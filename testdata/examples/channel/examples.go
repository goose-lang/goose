package chan_spec_raw_examples

import (
	"strings"

	"github.com/goose-lang/goose/model/channel"
)

// These are hand-translated examples that will be useful for demonstrating
// and adjusting specs prior to implementing translation.

// Example 1: Simple goroutine sending a string, check basic message passing without
// synchronization
func SendMessage() {
	// Create an unbuffered channel for the message
	messageChan := channel.NewChannelRef[string](0)

	// Start a goroutine to send the message
	go func() {
		messageChan.Send("hello world")
	}()

	// Receive the message
	message := messageChan.ReceiveDiscardOk()

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
	done := channel.NewChannelRef[uint64](0)

	// Launch goroutine
	go func() {
		// Set the message
		*message = "hello world"

		// Signal completion
		done.Send(0)
	}()

	// Join goroutine by receiving from channel
	done.ReceiveDiscardOk()

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
	done := channel.NewChannelRef[uint64](0)

	// Launch goroutine
	go func() {
		// Set the message
		*message = "hello world"

		// Wait for acknowledgment
		done.ReceiveDiscardOk()
	}()

	// Join goroutine by sending to channel
	done.Send(0)

	// Verify message was set correctly
	if *message != "hello world" {
		panic("Message was not set correctly")
	}
}

// Example 4: Broadcast notification with close. This is testing a case where
// we transfer disjoint ownership to different threads in a single broadcast
func BroadcastNotification() {
	// Create notification channel
	notifyCh := channel.NewChannelRef[uint64](0)

	// Create done channels for synchronization
	done1 := channel.NewChannelRef[uint64](0)
	done2 := channel.NewChannelRef[uint64](0)
	done3 := channel.NewChannelRef[uint64](0)

	// Create a list of 3 strings, initially empty
	var results []string
	results = append(results, "")
	results = append(results, "")
	results = append(results, "")

	// Start 3 goroutines
	go func() {
		// Wait for notification - read returns two values, but second value (ok) is important here
		_, ok := notifyCh.Receive()
		if !ok {
			// Channel was closed
			if results[0] != "thread1" {
				panic("Thread 1 received incorrect value")
			}
			done1.Send(0)
		}
	}()

	go func() {
		_, ok := notifyCh.Receive()
		if !ok {
			// Channel was closed
			if results[1] != "thread2" {
				panic("Thread 2 received incorrect value")
			}
			done2.Send(0)
		}
	}()

	go func() {
		_, ok := notifyCh.Receive()
		if !ok {
			// Channel was closed
			if results[2] != "thread3" {
				panic("Thread 3 received incorrect value")
			}
			done3.Send(0)
		}
	}()

	// Set values in the list
	results[0] = "thread1"
	results[1] = "thread2"
	results[2] = "thread3"

	// Close channel to notify all goroutines
	notifyCh.Close()

	// Wait for all goroutines to complete
	done1.ReceiveDiscardOk()
	done2.ReceiveDiscardOk()
	done3.ReceiveDiscardOk()
}

// Example 5: Join sending goroutine before closing a buffered channel.
// This should demonstrate the spec's ability to prevent closing on a channel
// without joining all the senders.
func CoordinatedChannelClose() {
	// Create a buffered channel
	bufCh := channel.NewChannelRef[uint64](2)

	// Create a synchronization channel
	syncCh := channel.NewChannelRef[uint64](0)

	// Start goroutine that sends to buffered channel
	go func() {
		bufCh.Send(42)
		// Signal completion
		syncCh.Send(0)
	}()

	// Send from main function
	bufCh.Send(84)

	// Wait for goroutine to complete sending
	syncCh.ReceiveDiscardOk()

	// Now safe to close the channel
	bufCh.Close()

	// Read all values - need to check the 'ok' flag for closed channels
	val1, ok1 := bufCh.Receive()
	val2, ok2 := bufCh.Receive()

	// Check that we got both values
	if !ok1 || !ok2 {
		panic("Channel shouldn't be empty yet")
	}

	if !((val1 == 42 && val2 == 84) || (val1 == 84 && val2 == 42)) {
		panic("Did not receive both expected values")
	}
}

// Example 6: A basic pipeline that just passes pointers
// to a single worker who doubles the value of what they
// point to.
func DoubleValues() {
	var val1 uint64 = 5
	var val2 uint64 = 10
	var val3 uint64 = 15

	var values []*uint64
	values = append(values, &val1)
	values = append(values, &val2)
	values = append(values, &val3)

	// Create an unbuffered channel for processing
	ch := channel.NewChannelRef[*uint64](0)
	done := channel.NewChannelRef[uint64](0)

	// Start a worker goroutine
	go func() {
		// Process each pointer using range
		for true {
			ptr, ok := ch.Receive()
			if !ok {
				break
			}
			*ptr = *ptr * 2
		}
		done.Close()
	}()

	// Send pointers to the goroutine for processing
	ch.Send(values[0])
	ch.Send(values[1])
	ch.Send(values[2])

	// Close the channel
	ch.Close()
	done.Receive()

	// Check if values were doubled correctly
	if !(val1 == 10 && val2 == 20 && val3 == 30) {
		panic("Values were not doubled correctly")
	}
}

// Equivalent runtime channel code:
//
//		func CapPipeline() string {
//		    // Input data
//		    input := []string{"hello", ",", " ", "world", "!"}
//
//		    // The pipe for the producer to send to the consumer.
//		    // Buffer size does not matter for correctness.
//		    data := make(chan string, 2)
//
//		    // Unbuffered channel to signal completion
//		    join := make(chan struct{})
//		    output := ""
//
//		    // Start goroutines
//		    go producer(input, data)
//		    go consumer(&output, data, join)
//
//		    // Wait for pipeline to be processed
//		    <-join
//	     	if output != "HELLO, WORLD!" {
//				panic("test failed, plus you can't verify this!")
//			}
//		}
func CapPipeline() {
	// Input data
	input := []string{"hello", ",", " ", "world", "!"}

	// The pipe for the producer to send to the consumer.
	// Buffer size does not matter for correctness.
	data := channel.NewChannelRef[string](2)

	// Unbuffered channel to signal completion
	join := channel.NewChannelRef[struct{}](0)
	output := ""

	// Start goroutines
	go producer(input, data)
	go consumer(&output, data, join)

	// Wait for pipeline to be processed
	join.ReceiveDiscardOk()
	if output != "HELLO, WORLD!" {
		panic("test failed, plus you can't verify this!")
	}
}

// Equivalent runtime channel Go code:
//
//	func producer(input []string, data chan<- string) {
//	    // Send each item
//	    for _, item := range input {
//	        data <- item
//	    }
//	    // Signal producer we’ve sent everything
//	    close(data)
//	}
func producer(input []string, data *channel.Channel[string]) {
	// Send each item
	for _, item := range input {
		data.Send(item)
	}
	// Signal consumer we’ve sent everything
	data.Close()
}

// Equivalent runtime channel Go code:
//
//	func consumer(output *string, data <-chan string, join chan<- struct{}) {
//	    // Keep receiving until channel is closed
//	    for item := range data {
//	        *output += strings.ToUpper(item)
//	    }
//
//	    // Tell main we’re done
//	    join <- struct{}{}
//	}
func consumer(output *string, data *channel.Channel[string], join *channel.Channel[struct{}]) {
	// Keep receiving until channel is closed(this is the model's range for loop).
	for {
		item, ok := data.Receive()
		if !ok {
			break
		}
		*output += strings.ToUpper(item)
	}

	// Tell main we’re done
	join.Send(struct{}{})
}

// Equivalent Go code:
//
//	func SelectRace() {
//	    alice := make(chan string, 1)
//	    bob := make(chan string, 1)
//	    result := ""
//
//	    // 2 goroutines race to write result and notify main that they won.
//	    // The loser's message will be ignored.
//	    go func() { alice <- "Alice wins" }()
//	    go func() { bob <- "Bob wins" }()
//
//	    select {
//	    case msg := <-alice:
//	        result = msg
//	    case msg := <-bob:
//	        result = msg
//	    }
//
//	    if !(result == "Alice wins" || result == "Bob wins") {
//	        panic("test failed, plus you can't verify this!")
//	    }
//	}
func SelectRace() {
	alice := channel.NewChannelRef[string](1)
	bob := channel.NewChannelRef[string](1)
	result := ""

	// 2 goroutines race to write result and notify main that they won.
	// The loser's message will be ignored.
	go func() { alice.Send("Alice wins") }()
	go func() { bob.Send("Bob wins") }()

	alice_case := channel.NewRecvCase(alice)
	bob_case := channel.NewRecvCase(bob)
	winner := channel.Select2(alice_case, bob_case, true)
	switch winner {
	case 0:
		result = alice_case.Value
	case 1:
		result = bob_case.Value
	}

	if !(result == "Alice wins" || result == "Bob wins") {
		panic("test failed, plus you can't verify this!")
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

// Equivalent Go runtime channel code:
//
//	func client(input []string, freeList chan []byte, serverChan chan []byte) {
//		for _, letter := range input {
//			var b []byte
//
//			// Non-blocking receive from freeList.
//			select {
//			case b = <-freeList:
//				// Reuse buffer from pool.
//			default:
//				// Allocate a new minimal buffer.
//				b = []byte{0}
//			}
//
//			load(&b, letter) // Put one letter into the buffer.
//			serverChan <- b  // Blocking send to server.
//		}
//
//		// Signal no more work.
//		close(serverChan)
//	}
func client(input []string, freeList *channel.Channel[[]byte], serverChan *channel.Channel[[]byte]) {
	for _, letter := range input {
		var b []byte
		// Non-blocking receive from freeList using Select1(case, false).
		rc := channel.NewRecvCase(freeList)
		if channel.Select1(rc, false) {
			// Selected: reuse buffer from pool.
			b = rc.Value
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

// Equivalent Go runtime code:
//
//	func server(output *string, freeList chan []byte, serverChan chan []byte, done chan struct{}) {
//		for {
//			// Blocking receive from serverChan.
//			b, ok := <-serverChan
//			if !ok {
//				// Channel closed and drained.
//				done <- struct{}{}
//				return
//			}
//
//			process(&b, output)
//
//			// Non-blocking return of buffer to freeList; drop if pool full.
//			select {
//			case freeList <- b:
//				// Returned to pool.
//			default:
//				// Pool full; drop buffer.
//			}
//		}
//	}
func server(output *string, freeList *channel.Channel[[]byte], serverChan *channel.Channel[[]byte], join *channel.Channel[struct{}]) {
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
		sc := channel.NewSendCase(freeList, b)
		channel.Select1(sc, false)

	}
}

// Equivalent Go runtime code:
//
//	func LeakyBufferPipeline() {
//		freeList := make(chan []byte, 5) // buffer pool
//		serverChan := make(chan []byte, 0)
//		done := make(chan struct{}, 0)
//
//		output := ""
//
//		go server(&output, freeList, serverChan, done)
//		client([]string{"h", "e", "l", "l", "o", ",", " ", "w", "o", "r", "l", "d"}, freeList, serverChan)
//		<-done
//
//		// At this point, server finished because client closed serverChan.
//		if output != "HELLO, WORLD" {
//			panic("unexpected pipeline output: " + output)
//		}
//	}
func LeakyBufferPipeline() {
	freeList := channel.NewChannelRef[[]byte](0) // buffer pool
	serverChan := channel.NewChannelRef[[]byte](0)
	join := channel.NewChannelRef[struct{}](0)

	output := ""

	go server(&output, freeList, serverChan, join)
	client([]string{"h", "e", "l", "l", "o", ",", " ", "w", "o", "r", "l", "d"}, freeList, serverChan)
	// Wait for processing to finish
	join.Receive()

	// At this point, server finished because client closed serverChan.
	if output != "HELLO, WORLD" {
		panic("unexpected pipeline output: " + output)
	}
}
