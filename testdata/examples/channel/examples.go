package chan_spec_raw_examples

import "github.com/goose-lang/goose/model/channel"

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
