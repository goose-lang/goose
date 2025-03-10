package channel

import (
	"sync"
)

type ChannelState uint64

const (
	// Only start and closed_final used for buffered channels.
	start                ChannelState = 0
	receiver_ready       ChannelState = 1
	sender_ready         ChannelState = 2
	receiver_done        ChannelState = 3
	sender_done          ChannelState = 4
	closed_receiver_done ChannelState = 5
	closed_sender_done   ChannelState = 6
	closed_final         ChannelState = 7
)

type Channel[T any] struct {
	lock  *sync.Mutex
	state ChannelState

	// Values only used for buffered channels. The length of buffer being 0 is how we determine a
	// channel is unbuffered. buffer is a circular queue that represents the channel's buffer
	buffer []T
	first  uint64
	count  uint64

	// Values only used for unbuffered channels
	v T
}

// buffer_size = 0 is an unbuffered channel
func NewChannel[T any](buffer_size uint64) Channel[T] {
	return Channel[T]{
		buffer: make([]T, buffer_size),
		lock:   new(sync.Mutex),
		first:  0,
		count:  0,
		state:  start,
	}
}

// buffer_size = 0 is an unbuffered channel
func NewChannelRef[T any](buffer_size uint64) *Channel[T] {
	return &Channel[T]{
		buffer: make([]T, buffer_size),
		lock:   new(sync.Mutex),
		first:  0,
		count:  0,
		state:  start,
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
			if c.state == closed_final {
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
			// Any of the closed states mean we should panic since we just entered Send.
			if (c.state == closed_final) || (c.state == closed_receiver_done) || (c.state == closed_sender_done) {
				panic("send on closed channel")
			}
			// Receiver waiting
			if c.state == receiver_ready {
				// Tell the receiver we have sent a value
				c.state = sender_done
				// Tell the receiver the value we are sending
				c.v = val
				c.lock.Unlock()
				return_early = true
				break
			}
			// No other senders/receivers have initiated a channel exchange so we can.
			if c.state == start {
				// Send our value
				c.v = val
				// Tell receivers we have sent a value
				c.state = sender_ready
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
				// A close may have happened in between but we still must observe that the
				// receiver knows we are done.
				if !(c.state == sender_done || c.state == closed_sender_done) {
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
			// We need to check if we have closed without the receiver seeing our value, which
			// means that close happened before a receiver arrived..
			if c.state == closed_final {
				panic("send on closed channel")
			}
			// If a receiver is done but we closed after, we can still complete the exchange
			// and don't have to panic since the close happened after a successful send/
			// receive exchange.
			if c.state == closed_receiver_done {
				c.state = closed_final
				c.lock.Unlock()
				break
			}
			if c.state == receiver_done {
				c.state = start
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
			if (c.state == closed_final) && c.count == 0 {
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
			// Any closed state means we return null and ok=false since we just entered
			// Receive.
			if (c.state == closed_final) || (c.state == closed_receiver_done) || (c.state == closed_sender_done) {
				c.lock.Unlock()
				closed = true
				break
			}
			// Sender is waiting
			if c.state == sender_ready {
				// Inform the sender we have received the value
				c.state = receiver_done
				// Save the value
				ret_val = c.v
				c.lock.Unlock()
				return_early = true
				break
			}
			// No channel operations are in progress so we can initiate an exchange
			if c.state == start {
				// Inform the next sender that we are ready to receive.
				c.state = receiver_ready
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
				// Close might happen in between but we still must wait for the sender to
				// observe that we have received their value.
				if !(c.state == receiver_done || c.state == closed_receiver_done) {
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
			// Close happened before sender could queue a value
			if c.state == closed_final {
				c.lock.Unlock()
				closed = true
				break
			}
			// If a close happened but a sender queued a value for us first, we can take the
			// value without returning null and set the state to closed_final so it is
			// acknowledged as closed in future exchanges.
			if c.state == closed_sender_done {
				// Reset sender flag
				c.state = closed_final
				// Save value
				ret_val = c.v
				c.lock.Unlock()
				break
			}
			if c.state == sender_done {
				// Reset sender flag
				c.state = start
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
	// Any of these states indicate that we are trying to close multiple times.
	if c.state == closed_final || c.state == closed_receiver_done || c.state == closed_sender_done {
		panic("close of closed channel")
	}
	// For buffered channels, this is the only state that we need to communicate closed, since
	// receivers can simply check if there are queued values and senders can panic.
	c.state = closed_final
	// If an exchange was successful but the parties are still waiting on this to be
	// acknowledged, we use the closed_..._done stages to allow the exchange to complete
	// before the state is set to closed_final. This is because we want a successful exchange
	// to complete if there was a waiting sender and receiver that pair up before we close.
	// Without these states we would lose a value.
	if c.state == receiver_done {
		c.state = closed_receiver_done
	}
	if c.state == sender_done {
		c.state = closed_sender_done
	}
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
// else block translation should be equivalent from a correctness perspective. There is at least 1
// notable unsound property with this approach:
// 1. Once a channel is closed, a receive case statement on said channel will always be selectable.
// This means that after the channel is closed, this case statement will always be selected above
// other statements below. This is considered an antipattern in the Go community and it is
// recommended that if a select case permits a closed channel receive, the channel is set to nil so
// that the statement will no longer be selectable. We can prevent this with the specfication by
// forcing the receiver to renounce receive ownership after receiving on a closed channel.
//
// One approach for making 1. sound would be to do the following for select statements:
// 1. Create a mutex guarded "winner_index" int
// 2. Launch a goroutine for each channel in the select with an index for the select cases
// (For selects with multiple cases for a single channel, we still have just 1 goroutine)
// 3. Lock the associated channel in each goroutine
// 4. If there is a case for a channel that is "immediately selectable" i.e the channel is closed
// or in the receiver/sender_ready state for the sender/receiver respectively, lock the
// winner_index mutex and if not already set, set the winner_index to the goroutine's index
// 5. If winner_index was set, complete the exchange and run the case's body
// 6. Join the above goroutines and if no winner is selected, go through the if/else TryReceive/
// TrySend sequence that we currently use.
//
// This would make it so the race to setting winner_index simulates the randomness of
// Go select statements where any selectable case has uniform probablity of being selected
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
			if c.state == closed_final {
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
		var offer bool = false
		c.lock.Lock()
		// Any of these states mean we closed before we attempt to receive, which means this
		// is selectable and we should return null and ok=false
		if c.state == closed_final || c.state == closed_receiver_done || c.state == closed_sender_done {
			closed = true
			selected = true
		} else {
			// Sender is waiting, get the value.
			if c.state == sender_ready {
				// Inform the sender that we have the value
				c.state = receiver_done
				// Save the value
				ret_val = c.v
				selected = true
			}
			// If we are in the start state, we still need to communicate that we are trying
			// to receive. To do this we will make an "offer" by setting the receiver_ready
			// flag and then we will check it immediately to see if a sender happened to
			// arrive. This does not have great performance characteristics since we rely on
			// the thread to be immediately preempted and a sender to arrive and see
			// receiver_ready in between but for liveness purposes it needs to at least be
			// possible for an exchange to happen between 2 threads doing blocking selects
			// with Send/Receive on the same channel.
			if c.state == start {
				c.state = receiver_ready
				offer = true
			}
		}
		c.lock.Unlock()
		if offer {
			c.lock.Lock()
			// Offer was accepted
			if c.state == sender_done {
				ret_val = c.v
				c.state = start
				selected = true
			}
			// Revoke our offer if it still stands(Close can revoke it for us)
			if c.state == receiver_ready {
				c.state = start
			}
			c.lock.Unlock()
		}
		if closed {
			return selected, ret_val, !closed
		}
		// If we received a value, wait until the sender knows that we received the value to
		// complete the exchange.
		if selected && !offer {
			for {
				c.lock.Lock()
				if !(c.state == receiver_done || c.state == closed_receiver_done) {
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
		if c.state == closed_final {
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
		var offer bool = false
		c.lock.Lock()
		if c.state == closed_final || c.state == closed_receiver_done || c.state == closed_sender_done {
			panic("send on closed channel")
		}

		// If we're not closed and a receiver is waiting, we can send them the value
		if c.state == receiver_ready {
			c.state = sender_done
			c.v = val
			selected = true
		}
		// If we are in the start state, make an offer for a possible receiver. We will only
		// leave this offer open until we almost immediately lock again and check the result
		// but this is necessary to ensure liveness when there are multiple goroutines running
		// blocking select statements that would match.
		if c.state == start {
			c.state = sender_ready
			c.v = val
			offer = true
		}
		c.lock.Unlock()
		if offer {
			c.lock.Lock()
			if c.state == receiver_done || c.state == closed_receiver_done {
				c.state = start
				selected = true
			}
			if c.state == sender_ready {
				c.state = start
			}
			c.lock.Unlock()
		}
		// This is necessary to make sure that the receiver has consumed our sent value. If we
		// don't do this, a sender can unblock and potentially close the channel before the
		// receiver has had a chance to consume it which would not be the same behavior as Go
		// channels.
		if selected && !offer {
			for {
				c.lock.Lock()
				if !(c.state == sender_done || c.state == closed_sender_done) {
					c.lock.Unlock()
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
