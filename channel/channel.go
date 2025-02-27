package channel

import (
	"sync"
)

type Channel[T any] struct {
	lock   *sync.Mutex
	closed bool

	// Values only used for buffered channels. The length of buffer being 0 is how we determine a
	// channel is unbuffered. buffer is a circular queue that represents the channel's buffer
	buffer []T
	first  uint64
	count  uint64

	// Values only used for unbuffered channels
	v              T
	receiver_ready bool
	sender_ready   bool
	receiver_done  bool
	sender_done    bool
}

// buffer_size = 0 is an unbuffered channel
func NewChannel[T any](buffer_size uint64) Channel[T] {
	return Channel[T]{
		buffer: make([]T, buffer_size),
		lock:   new(sync.Mutex),
		first:  0,
		count:  0,
	}
}

// buffer_size = 0 is an unbuffered channel
func NewChannelRef[T any](buffer_size uint64) *Channel[T] {
	return &Channel[T]{
		buffer: make([]T, buffer_size),
		lock:   new(sync.Mutex),
		first:  0,
		count:  0,
	}
}

// c.Send(val)
//
// is equivalent to:
//
// c <- val
func (c *Channel[T]) Send(val T) {
	if c == nil {
		// Block forever
		for {
		}
	}
	var buffer_size uint64 = uint64(len(c.buffer))
	// Buffered channel. In this case we can simply wait for space in the queue and queue our value.
	if buffer_size != 0 {
		for {
			c.lock.Lock()
			if c.closed {
				panic("send on closed channel")
			}
			// No room to buffer the value
			if c.count >= buffer_size {
				c.lock.Unlock()
				continue
			}
			// emplace the value in the circular queue
			var last uint64 = (c.first + c.count) % buffer_size
			c.buffer[last] = val
			c.count += 1
			c.lock.Unlock()
			break
		}
		// Unbuffered channel. This is more complex since the sender must wait for a receiver to be
		//  waiting and also wait for the receiver to acknowledge that it has received the value
		// before moving on.
	} else {

		// Set to true if the receiver arrives before the sender
		var return_early = false

		// Wait for either
		// 1. A receiver waiting for a value to be sent
		// 2. No channel operations are in progress, meaning we can communicate that we are a
		// waiting sender to the next receiver that arrives.
		for {
			c.lock.Lock()
			if c.closed {
				panic("send on closed channel")
			}
			// Receiver waiting
			if c.receiver_ready {
				// Reset the receiver's waiting flag
				c.receiver_ready = false
				// Tell the receiver we have sent a value
				c.sender_done = true
				// Tell the receiver the value we are sending
				c.v = val
				c.lock.Unlock()
				return_early = true
				break
			}
			// No other senders/receivers have initiated a channel exchange so we can.
			if !c.receiver_ready && !c.sender_ready && !c.receiver_done && !c.sender_done {
				// Send our value
				c.v = val
				// Tell receivers we have sent a value
				c.sender_ready = true
				c.lock.Unlock()
				break
			}
			c.lock.Unlock()
		}

		// If we arrived second, we still have to wait for the receiver to acknowledge that they
		// have received our value so that the sender cannot continue and potentially close the
		// channel before the receiver has completed the exchange, which would differ from the
		// behavior of Go channels.
		if return_early {
			for {
				c.lock.Lock()
				if !c.sender_done {
					c.lock.Unlock()
					break
				}
				c.lock.Unlock()
			}
			return
		}
		// We have arrived first, wait for the receiver to acknowledge that they have received our
		// value.
		for {
			c.lock.Lock()
			// We need to check closed again here. If we queued are value before another channel
			// closed, we will must panic.
			if c.closed {
				panic("send on closed channel")
			}
			if c.receiver_done {
				c.receiver_done = false
				c.lock.Unlock()
				break
			}
			c.lock.Unlock()
		}
	}
}

// Equivalent to:
// value, ok := <-c
// Notably, this requires the user to consume the ok bool which is not actually required with Go
// channels. This should be able to be solved by adding an overload wrapper that discards the ok
// bool.
func (c *Channel[T]) Receive() (T, bool) {
	if c == nil {
		// Block forever
		for {
		}
	}
	var ret_val T
	var buffer_size uint64 = uint64(len(c.buffer))
	var closed = false

	// Buffered channel, we can simply block until a value is in the buffer then dequeue it from
	// the buffer.
	if buffer_size != 0 {
		for {
			c.lock.Lock()
			if c.closed && c.count == 0 {
				c.lock.Unlock()
				closed = true
				break
			}
			if c.count == 0 {
				c.lock.Unlock()
				continue
			}
			ret_val = c.buffer[c.first]
			c.first = (c.first + 1) % buffer_size
			c.count -= 1
			c.lock.Unlock()
			break
		}
		return ret_val, !closed
		// Unbuffered channel. This logic is more complex since we need to make sure the exchange
		// doesn't begin until a sender is ready and doesn't end until the sender knows the
		// receiver has received the value.
	} else {

		var return_early = false
		for {
			c.lock.Lock()
			if c.closed {
				c.lock.Unlock()
				closed = true
				break
			}
			// Sender is waiting
			if c.sender_ready {
				// Reset sender waiting flag
				c.sender_ready = false
				// Inform the sender we have received the value
				c.receiver_done = true
				// Save the value
				ret_val = c.v
				c.lock.Unlock()
				return_early = true
				break
			}
			// No channel operations are in progress so we can initiate an exchange
			if !c.receiver_ready && !c.sender_ready && !c.receiver_done && !c.sender_done {
				// Inform the next sender that we are ready to receive.
				c.receiver_ready = true
				c.lock.Unlock()
				break
			}
			c.lock.Unlock()
		}
		if closed {
			return ret_val, !closed
		}
		// If the sender arrived first, we still must wait for them to acknowledge that the .
		// exchange is complete.
		if return_early {
			for {
				c.lock.Lock()
				if !c.receiver_done {
					c.lock.Unlock()
					break
				}
				c.lock.Unlock()
			}
			return ret_val, !closed
		}
		// Receiver arrived first, wait for sender to arrive and queue value for us.
		for {
			c.lock.Lock()
			if c.closed {
				c.lock.Unlock()
				closed = true
				break
			}
			if c.sender_done {
				// Reset sender flag
				c.sender_done = false
				// Save value
				ret_val = c.v
				c.lock.Unlock()
				break
			}
			c.lock.Unlock()
		}
		return ret_val, !closed
	}
}

// c.Close()
//
// is equivalent to:
//
// close(c)
func (c *Channel[T]) Close() {
	if c == nil {
		panic("close of nil channel")
	}
	c.lock.Lock()
	if c.closed {
		panic("close of closed channel")
	}
	// For Unbuffered channels, we set these false since there may be waiting senders and receivers
	// before Close() is called. This will ensure that the waiting senders panic and waiting
	// receivers return the null value. For buffered channels, senders check for closed on every
	// loop iteration while waiting for a value to become available and receivers can simply
	// dequeue values without checking for closed since real Go buffered channels do not return the
	// null value on a closed channel receive until there are no more buffered values.
	c.receiver_ready = false
	c.sender_ready = false
	c.closed = true
	c.lock.Unlock()
}

// v := c.ReceiveDiscardOk
//
// is equivalent to:
// v := c<-
// It seems like Go requires ignored return values to be annotated with _ but channels don't
// require this so this will need to be translated.
func (c *Channel[T]) ReceiveDiscardOk() T {
	var return_val T
	return_val, _ = c.Receive()
	return return_val
}

// This:
//
//	for {
//		selected, val, ok := ch.TryReceive()
//		if !ok {
//			break
//		}
//		if selected {
//			<body>
//		}
//	}
//
// is equivalent to:
//
//	for v := <-ch {
//			<body>
//	}
//
// This:
//
//	selected, val, ok := c.TryReceive()
//	if selected {
//		<first case body>
//	} else {
//		selected = c.TrySend(0)
//		if selected {
//			<second case body>
//		} else {
//			<default block body>
//		}
//	}
//
// is equivalent to:
//
//	select {
//		case <-c:
//			<first case body>
//		case c <- 0:
//			<second case body>
//		default:
//			<default body>
//		}
//
// This:
//
//	for {
//		selected, val, ok := c.TryReceive()
//		if selected {
//			<first case body>
//			break
//		} else {
//			selected = c.TrySend(0)
//			if selected {
//				<second case body>
//				break
//			}
//		}
//	}
//
// is equivalent to:
//
//	select {
//		case <-c:
//			<first case body>
//		case c <- 0:
//			<second case body>
//		}
//
// Note: Technically speaking, Go only compiles select statements to if/else blocks when there is 1
// case statement with a default block. When there are multiple statements, the Go code will choose
// a case statement with uniform probability among all "selectable" statements, meaning those that
// have a waiting sender/receiver on the other end and receives on closed channels. Since threading
// behavior means that it already can't be assumed with certainty which blocks are selected, the if/
// else block translation should be equivalent from a correctness perspective. There are at least 2
// notable unsound property with this approach:
// 1. Once a channel is closed, a receive case statement on said channel will always be selectable.
// This means that after the channel is closed, this case statement will always be selected above
// other statements below. This is considered an antipattern in the Go community and it is
// recommended that if a select case permits a closed channel receive, the channel is set to nil so
// that the statement will no longer be selectable. We can prevent this with the specfication by
// forcing the receiver to renounce receive ownership after receiving on a closed channel.
// 2. When there are multiple blocking select statements(no default case) with 2 cases: a send and
// a receive statement on the same unbuffered channel running concurrently, this model's
// implementation will livelock since neither goroutine will communicate to the other that it is
// waiting with a matching send/receive statement, so TrySend/TryReceive will fail repeatedly. See
// TestSelfSelect in https://go.dev/src/runtime/chan_test.go for the unit test that brought
// attention to this issue.
//
// We will eventually be able to make this model sound for 1. once we have support for random
// permutations using a similar approach to dynamic select statements in the reflect package but for
// now our specification will prevent code that isn't equivalent from being verified which should
// be good enough.
//
// For 2, I believe that if we have support for random numbers we can implement blocking select
// statements with unbuffered channels by randomly selecting a case with an unbuffered channel
// using the following algorithm:
// 1. Attempt each case's channel operation with TrySend/TryReceive. If one of them succeeds,
// select this case and execute its block
// 2. For each case statement with an unbuffered channel, lock the associated channel
// 3. Randomly select an unbuffered channel and set the sender_ready or receiver_ready flag for a
// Send/Receive operation respectively.
// 4. Unlock all of the unbuffered channels
// 5. Lock the channel that was chosen in step 3 and if the ready flag has been set to false,
// continue the send/receive using the same procedure as Send()/Receive(), unlock the channel and
// execute the associated case block
// 6. Otherwise, unlock the channel and go back to step 1.
// This is not particularly graceful and relies on the sending thread being preempted in between
// steps 4 and 5 and the goroutine with the goroutine executing the matching select statement
// acquiring the lock in between but it should eventually be able to make progress eventually. This
// is indeed a tough edge case for real channels as well as it breaks an otherwise powerful
// invariant as described in the comment on line 10 in the runtime
// implementation(https://go.dev/src/runtime/chan.go), so I don't think there will be a
// particularly graceful solution here. I also don't know of any useful patterns that would require
// a select statement of this sort so it may be worth it to fix this problem lazily i.e. if/when a
// use case happens to call for it in the future.
//
// Note: The above code technically makes it so the top block's expression variables
// are in scope in all of the other blocks. This would error in the Go code before it is translated
// so this shouldn't matter for practical purposes.
func (c *Channel[T]) TryReceive() (bool, T, bool) {
	var ret_val T
	if c == nil {
		return false, ret_val, false
	}
	var buffer_size uint64 = uint64(len(c.buffer))
	var closed = false
	var selected = false
	// Buffered channel
	if buffer_size != 0 {
		c.lock.Lock()
		// No values available to dequeue, don't select unless channel is closed.
		if c.count == 0 {
			if c.closed {
				closed = true
				selected = true
			}
			c.lock.Unlock()
		} else {
			// Value is available, select and dequeue value
			ret_val = c.buffer[c.first]
			c.first = (c.first + 1) % buffer_size
			c.count -= 1
			selected = true
			c.lock.Unlock()
		}
		return selected, ret_val, !closed
		// Unbuffered channel. This logic is more complex since we need to make sure the exchange
		// doesn't occur unless a sender is ready and doesn't end until the sender knows the
		// receiver has received the value.
	} else {
		c.lock.Lock()
		if c.closed {
			closed = true
			selected = true
		} else {
			// Sender is waiting, get the value.
			if c.sender_ready {
				// Reset the sender's waiting flag
				c.sender_ready = false
				// Inform the sender that we have the value
				c.receiver_done = true
				// Save the value
				ret_val = c.v
				selected = true
			}
		}
		c.lock.Unlock()
		if closed {
			return selected, ret_val, !closed
		}
		// If we received a value, wait until the sender knows that we received the value to
		// complete the exchange.
		if selected {
			for {
				c.lock.Lock()
				if !c.receiver_done {
					c.lock.Unlock()
					break
				}
				c.lock.Unlock()
			}
		}
		return selected, ret_val, !closed
	}
}

// See comment in TryReceive for how this is used to translate selects.
func (c *Channel[T]) TrySend(val T) bool {
	// Nil is not selectable
	if c == nil {
		return false
	}
	var selected = false
	var buffer_size uint64 = uint64(len(c.buffer))

	// Buffered channel
	if buffer_size != 0 {
		c.lock.Lock()
		if c.closed {
			panic("send on closed channel")
		}
		// If we have room, buffer our value
		if !(c.count >= buffer_size) {
			var last uint64 = (c.first + c.count) % buffer_size
			c.buffer[last] = val
			c.count += 1
			selected = true
		}
		c.lock.Unlock()
		return selected
		// Unbuffered channel
	} else {
		c.lock.Lock()
		if c.closed {
			panic("send on closed channel")
		}

		// If we're not closed and a receiver is waiting, we can send them the value
		if c.receiver_ready {
			c.receiver_ready = false
			c.sender_done = true
			c.v = val
			selected = true
		}
		c.lock.Unlock()
		// This is necessary to make sure that the receiver has consumed our sent value. If we
		// don't do this, a sender can unblock and potentially close the channel before the
		// receiver has had a chance to consume it which would not be the same behavior as Go
		// channels.
		if selected {
			for {
				c.lock.Lock()
				if !c.sender_done {
					break
				}
				c.lock.Unlock()
			}
		}
		return selected
	}
}

// c.Len()
//
// is equivalent to:
// len(c)
//
// This might not be worth specifying since it is hard to make good use of channel length
// semantics.
func (c *Channel[T]) Len() uint64 {
	if c == nil {
		return 0
	}
	var chan_len uint64 = 0
	c.lock.Lock()
	chan_len = c.count
	c.lock.Unlock()
	return chan_len
}

// c.Cap()
//
// is equivalent to:
// cap(c)
func (c *Channel[T]) Cap() uint64 {
	if c == nil {
		return 0
	}
	return uint64(len(c.buffer))
}
