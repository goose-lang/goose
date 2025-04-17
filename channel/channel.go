package channel

import (
	"sync"

	"github.com/goose-lang/primitive"
)

type ChannelState uint64

const (
	// Only start and closed used for buffered channels.
	start          ChannelState = 0
	receiver_ready ChannelState = 1
	sender_ready   ChannelState = 2
	receiver_done  ChannelState = 3
	sender_done    ChannelState = 4
	closed         ChannelState = 5
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
			if c.state == closed {
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
			if c.state == closed {
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
				if !(c.state == sender_done) {
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
			if c.state == closed {
				panic("send on closed channel")
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
	var closed_local = false

	// Buffered channel, we can simply block until a value is in the buffer then dequeue it from
	// the buffer.
	if buffer_size != 0 {
		for {
			c.lock.Lock()
			if (c.state == closed) && c.count == 0 {
				c.lock.Unlock()
				closed_local = true
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
		return ret_val, !closed_local
		// Unbuffered channel. This logic is more complex since we need to make sure the exchange
		// doesn't begin until a sender is ready and doesn't end until the sender knows the
		// receiver has received the value.
	} else {

		var return_early = false
		for {
			c.lock.Lock()
			// Any closed state means we return null and ok=false since we just entered
			// Receive.
			if c.state == closed {
				c.lock.Unlock()
				closed_local = true
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
		if closed_local {
			return ret_val, !closed_local
		}
		// If the sender arrived first, we still must wait for them to acknowledge that the .
		// exchange is complete.
		if return_early {
			for {
				c.lock.Lock()
				// Close might happen in between but we still must wait for the sender to
				// observe that we have received their value.
				if !(c.state == receiver_done) {
					c.lock.Unlock()
					break
				}
				c.lock.Unlock()
			}
			return ret_val, !closed_local
		}
		// Receiver arrived first, wait for sender to arrive and queue value for us.
		for {
			c.lock.Lock()
			// Close happened before sender could queue a value
			if c.state == closed {
				c.lock.Unlock()
				closed_local = true
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
		return ret_val, !closed_local
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
	for {
		c.lock.Lock()
		if c.state == closed {
			panic("close of closed channel")
		}
		// For unbuffered channels, if there is an exchange in progress, let the exchange complete.
		// In the real channel code the lock is held while this happens.
		if c.state == receiver_done || c.state == sender_done {
			c.lock.Unlock()
			continue
		}
		c.state = closed
		c.lock.Unlock()
		break
	}
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

// A non-blocking receive operation. If there is not a sender available in an unbuffered channel,
// we "offer" for a single program step by setting receiver_ready to true, unlocking, then
// immediately locking, which is necessary when a potential matching party is using TrySend.
// See the various <n>CaseSelect functions for a description of how this is used to model selects.
func (c *Channel[T]) TryReceive() (bool, T, bool) {
	var ret_val T
	if c == nil {
		return false, ret_val, false
	}
	var buffer_size uint64 = uint64(len(c.buffer))
	var closed_local = false
	var selected = false
	// Buffered channel
	if buffer_size != 0 {
		c.lock.Lock()
		// No values available to dequeue, don't select unless channel is closed.
		if c.count == 0 {
			if c.state == closed {
				closed_local = true
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
		return selected, ret_val, !closed_local
		// Unbuffered channel. This logic is more complex since we need to make sure the exchange
		// doesn't occur unless a sender is ready and doesn't end until the sender knows the
		// receiver has received the value.
	} else {
		var offer bool = false
		c.lock.Lock()
		// Any of these states mean we closed before we attempt to receive, which means this
		// is selectable and we should return null and ok=false
		if c.state == closed {
			closed_local = true
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
		if closed_local {
			return selected, ret_val, !closed_local
		}
		// If we received a value, wait until the sender knows that we received the value to
		// complete the exchange.
		if selected && !offer {
			for {
				c.lock.Lock()
				if !(c.state == receiver_done) {
					c.lock.Unlock()
					break
				}
				c.lock.Unlock()
			}
		}
		return selected, ret_val, !closed_local
	}
}

// A non-blocking send operation. If there is not a receiver available in an unbuffered channel,
// we "offer" for a single program step by setting sender_ready to true, unlocking, then
// immediately locking, which is necessary when a potential matching party is using TryReceive.
// See the various <n>CaseSelect functions for a description of how this is used to model selects.
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
		if c.state == closed {
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
		if c.state == closed {
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
			if c.state == receiver_done {
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
				if !(c.state == sender_done) {
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

type SelectDir uint64

const (
	SelectSend    SelectDir = 0 // case Chan <- Send
	SelectRecv    SelectDir = 1 // case <-Chan:
	SelectDefault SelectDir = 2 // default
)

// value is used for the value the sender will send and also used to return the received value by
// reference.
type SelectCase[T any] struct {
	channel *Channel[T]
	dir     SelectDir
	Value   T
	Ok      bool
}

// Models a 2 case select statement. Returns 0 if case 1 selected, 1 if case 2 selected.
// Requires that case 1 not have dir = SelectDefault. If case_2 is a default, this will never block.
// This is similar to the reflect package dynamic select statements and should give us a true to
// runtime Go model with a fairly intuitive spec/translation.
//
//	This:
//	select {
//		case c1 <- 0:
//			<case 1 body>
//		case v, ok := <-c2:
//			<case 2 body>
//	}
//
//	Will be translated to:
//
// case_1 := channel.NewSendCase(c1, 0)
// case_2 := channel.NewRecvCase(c2)
// var uint64 selected_case = TwoCaseSelect(case_1, case_2)
//
//	if selected_case == 0 {
//		<case 1 body>
//	}
//	if selected_case == 1 {
//			var ok bool = case_2.ok
//			var v uint64 = case_2.value
//			<case 2 body>
//		}
func TwoCaseSelect[T1 any, T2 any](case_1 *SelectCase[T1], case_2 *SelectCase[T2]) uint64 {
	var selected_case uint64 = 0
	var selected bool = false
	// A "random" shuffle for correctness purposes, but probably mostly will be the same.
	var order []uint64 = Shuffle(2)
	for {
		for _, i := range order {
			// Perennial doesn't support breaks inside of nested for loops, so just don't do this
			// if we have selected something already
			if i == 0 && !selected {
				selected = TrySelect(case_1)
				if selected {
					selected_case = 0
				}
			}
			// Make sure we don't select default preferentially
			if i == 1 && !selected && case_2.dir != SelectDefault {
				selected = TrySelect(case_2)
				if selected {
					selected_case = 1
				}
			}
		}
		if !selected && case_2.dir == SelectDefault {
			break
		}
		// If case_2 is a default, this will always be true on the first iteration, so this
		// doesn't block in that case.
		if selected {
			break
		}
	}
	return selected_case
}

func ThreeCaseSelect[T1 any, T2 any, T3 any](case_1 *SelectCase[T1], case_2 *SelectCase[T2], case_3 *SelectCase[T3]) uint64 {
	var selected_case uint64 = 0
	var selected bool = false
	var order []uint64 = Shuffle(3)
	for {
		for _, i := range order {
			if i == 0 && !selected {
				selected = TrySelect(case_1)
				if selected {
					selected_case = 0
				}
			}
			if i == 1 && !selected {
				selected = TrySelect(case_2)
				if selected {
					selected_case = 1
				}
			}
			if i == 2 && !selected && case_3.dir != SelectDefault {
				selected = TrySelect(case_3)
				if selected {
					selected_case = 2
				}
			}
		}
		if !selected && case_3.dir == SelectDefault {
			break
		}
		if selected {
			break
		}
	}
	return selected_case
}

// Uses the applicable Try<Operation> function on the select case's channel. Default is always
// selectable so simply returns true.
func TrySelect[T any](select_case *SelectCase[T]) bool {
	var channel *Channel[T] = select_case.channel
	if select_case.dir == SelectSend {
		return channel.TrySend(select_case.Value)
	}
	if select_case.dir == SelectRecv {
		var item T
		var ok bool
		var selected bool
		selected, item, ok = channel.TryReceive()
		// We can use these values for return by reference and they will be implicitly kept alive
		// by the garbage collector so we can use value here for both the send and receive
		// variants. What a miracle it is to not be using C++.
		select_case.Value = item
		select_case.Ok = ok
		return selected

	}
	if select_case.dir == SelectDefault {
		return true
	}
	return false
}

// Simple knuth shuffle.
func Shuffle(n uint64) []uint64 {
	var order = make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		order[i] = uint64(i)
	}
	for i := uint64(len(order) - 1); i > 0; i-- {
		var j uint64 = primitive.RandomUint64() % uint64(i+1)
		var temp uint64 = order[i]
		order[i] = order[j]
		order[j] = temp
	}
	return order
}

func NewSendCase[T any](channel *Channel[T], value T) SelectCase[T] {
	return SelectCase[T]{
		channel: channel,
		dir:     SelectSend,
		Value:   value,
	}
}

func NewRecvCase[T any](channel *Channel[T]) SelectCase[T] {
	return SelectCase[T]{
		channel: channel,
		dir:     SelectRecv,
	}
}

// The type does not matter here, picking a simple primitive.
func NewDefaultCase() SelectCase[uint64] {
	return SelectCase[uint64]{
		dir: SelectDefault,
	}
}
