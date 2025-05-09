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

// Example 4: Broadcast notification with close. This is testing a case where
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

// Example 5: Join sending goroutine before closing a buffered channel.
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
