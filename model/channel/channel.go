package channel

import (
	"github.com/goose-lang/primitive"
)

type offerState uint64

const (
	buffered offerState = iota
	idle
	sndPending
	rcvPending
	sndCommit
	rcvDone
	closed
)

type Channel[T any] struct {
	cap int

	// mu protects all remaining fields
	mu    *primitive.Mutex
	state offerState
	// used only for buffered channels
	buffer []T
	// in-flight value used only for unbuffered channels
	v T
}

func NewChannel[T any](cap int) *Channel[T] {
	local_state := idle
	if cap > 0 {
		local_state = buffered
	}
	return &Channel[T]{
		cap:    cap,
		mu:     new(primitive.Mutex),
		buffer: make([]T, 0),
		state:  local_state,
	}
}

// c.Send(val)
//
// is equivalent to:
//
// c <- val
func (c *Channel[T]) Send(v T) {
	if c == nil {
		// Block forever
		for {
		}
	}
	for !c.TrySend(v, true) {
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
	for {
		success, v, ok := c.TryReceive(true)
		if success {
			return v, ok
		}
	}
}

// This is a non-blocking attempt at closing. The only reason close blocks ever is because there
// may be successful exchanges that need to complete, which is equivalent to the go runtime where
// the closer must still obtain the channel's lock
func (c *Channel[T]) tryClose() bool {
	c.mu.Lock()
	switch c.state {
	case closed:
		panic("close of closed channel")
	case idle, buffered:
		c.state = closed
		c.mu.Unlock()
		return true
	// For unbuffered channels, if there is an exchange in progress, let the exchange complete.
	// In the runtime channel code the lock is held while this happens.
	default:
		c.mu.Unlock()
		return false
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
	for !c.tryClose() {
	}
}

// v := c.ReceiveDiscardOk
//
// is equivalent to:
// v := c<-
func (c *Channel[T]) ReceiveDiscardOk() T {
	return_val, _ := c.Receive()
	return return_val
}

// Non-blocking receive function used for select statements.
// The blocking parameter here is used to determine whether or not we will make an offer to a
// waiting sender. If true, we will make an offer since blocking receive is modeled as a for loop
// around nonblocking TryReceive. If false, we don't make an offer since we don't need to match
// with another non-blocking send.
func (c *Channel[T]) TryReceive(blocking bool) (bool, T, bool) {
	var local_val T
	// First critical section: determine state and get value if sender is ready
	c.mu.Lock()
	switch c.state {
	case buffered:
		var v T
		if len(c.buffer) > 0 {
			val_copy := c.buffer[0]
			c.buffer = c.buffer[1:]
			c.mu.Unlock()
			return true, val_copy, true
		}
		c.mu.Unlock()
		return false, v, true
	case closed:
		// For a buffered channel, we drain the buffer before returning ok=false.
		if len(c.buffer) > 0 {
			val_copy := c.buffer[0]
			c.buffer = c.buffer[1:]
			c.mu.Unlock()
			return true, val_copy, true
		}
		c.mu.Unlock()
		return true, local_val, false
	// Sender is making an offer, accept it
	case sndPending:
		local_val = c.v
		c.state = rcvDone
		c.mu.Unlock()
		return true, local_val, true
	case idle:
		if blocking {
			c.state = rcvPending
			c.mu.Unlock()
			c.mu.Lock()
			switch c.state {
			// Offer wasn't accepted in time, rescind it.
			case rcvPending:
				c.state = idle
				c.mu.Unlock()
				return false, local_val, true
			// Offer was accepted, reset channel.
			case sndCommit:
				c.state = idle
				local_val = c.v
				c.mu.Unlock()
				return true, local_val, true
			default:
				// The protocol does not allow interference when an offer is outgoing.
				panic("not supposed to be here!")
			}
		}
		// For nonblocking, we can't make offers, only can complete them.
		c.mu.Unlock()
		return false, local_val, true
	// An exchange is in progress that we can't participate in.
	default:
		c.mu.Unlock()
		return false, local_val, true
	}
}

// Non-Blocking send operation for select statements. Blocking send and blocking select
// statements simply call this in a for loop until it returns true.
func (c *Channel[T]) TrySend(val T, blocking bool) bool {
	c.mu.Lock()
	switch c.state {
	case closed:
		panic("send on closed channel")
	case buffered:
		// If we have room, buffer our value
		if len(c.buffer) < int(c.cap) {
			c.buffer = append(c.buffer, val)
			c.mu.Unlock()
			return true
		}
		c.mu.Unlock()
		return false
	case rcvPending:
		// Receiver offers, accept offer.
		c.state = sndCommit
		c.v = val
		c.mu.Unlock()
		return true
	case idle:
		// Make an offer only if blocking.
		if blocking {
			c.state = sndPending
			// Save the value in case the receiver completes the exchange.
			c.v = val
			c.mu.Unlock()
			c.mu.Lock()
			switch c.state {
			// Receiver accepts, reset the channel.
			case rcvDone:
				c.state = idle
				c.mu.Unlock()
				return true
			// Offer still stands, rescind it.
			case sndPending:
				c.state = idle
				c.mu.Unlock()
				return false
			// This protocol doesn't work if other parties can cancel the exchange.
			default:
				panic("Invalid state transition with open receive offer")
			}
		}
		// Nonblocking sends can't make offers, only can accept them.
		c.mu.Unlock()
		return false
	// An exchange is in progress that we can't participate in.
	default:
		c.mu.Unlock()
		return false
	}
}

// c.Len()
//
// is equivalent to:
// len(c)
//
// This might not be worth specifying since it is hard to make good use of channel length
// semantics.
func (c *Channel[T]) Len() int {
	if c == nil {
		return 0
	}
	c.mu.Lock()
	chan_len := len(c.buffer)
	c.mu.Unlock()
	return chan_len
}

// c.Cap()
//
// is equivalent to:
// cap(c)
func (c *Channel[T]) Cap() int {
	if c == nil {
		return 0
	}
	return c.cap
}

// c.Iter() returns an iterator that models a for range loop over the channel.
func (c *Channel[T]) Iter() func(yield func(T) bool) {
	return func(yield func(T) bool) {
		for {
			selected, v, ok := c.TryReceive(true)
			// no progress this iteration, try again
			if !selected {
				continue
			}
			// iteration is done
			if !ok {
				return
			}
			if !yield(v) {
				// early exit
				return
			}
		}
	}
}

// The code below models select statements in a similar way to the reflect package's
// dynamic select statements. See unit tests in channel_test.go for examples of
// the intended translation.
type SelectDir uint64

const (
	SelectSend SelectDir = 0 // case ch <- Send
	SelectRecv SelectDir = 1 // case <-ch:
)

// Non-blocking select with 1 case (send or receive)
// For receive: value parameter is ignored
// Returns (selected, received_value, ok)
func NonBlockingSelect1[T any](ch *Channel[T], dir SelectDir, value T) (bool, T, bool) {
	var zero T

	if dir == SelectSend {
		selected := ch.TrySend(value, false)
		return selected, zero, false
	} else { // SelectRecv
		selected, recv_val, ok := ch.TryReceive(false)
		return selected, recv_val, ok
	}
}

// Blocking select with 2 cases
// Returns (caseIndex, received_value1, received_value2, ok)
func BlockingSelect2[T1, T2 any](
	ch1 *Channel[T1], dir1 SelectDir, val1 T1,
	ch2 *Channel[T2], dir2 SelectDir, val2 T2) (uint64, T1, T2, bool) {

	var zero1 T1
	var zero2 T2

	for {
		// Flip coin each iteration
		if primitive.RandomUint64()%2 == 0 {
			// Try case 1
			if dir1 == SelectSend {
				if ch1.TrySend(val1, true) {
					return 0, zero1, zero2, false
				}
			} else {
				selected, recv_val, ok := ch1.TryReceive(true)
				if selected {
					return 0, recv_val, zero2, ok
				}
			}
		} else {
			// Try case 2
			if dir2 == SelectSend {
				if ch2.TrySend(val2, true) {
					return 1, zero1, zero2, false
				}
			} else {
				selected, recv_val, ok := ch2.TryReceive(true)
				if selected {
					return 1, zero1, recv_val, ok
				}
			}
		}
	}
}

// Non-blocking select with 2 cases
// Returns (caseIndex, received_value1, received_value2, ok)
// caseIndex = 2 means no selection
func NonBlockingSelect2[T1, T2 any](
	ch1 *Channel[T1], dir1 SelectDir, val1 T1,
	ch2 *Channel[T2], dir2 SelectDir, val2 T2) (uint64, T1, T2, bool) {

	var zero1 T1
	var zero2 T2

	// Randomize which case to try first
	if primitive.RandomUint64()%2 == 0 {
		// Try case 1 first
		if dir1 == SelectSend {
			if ch1.TrySend(val1, false) {
				return 0, zero1, zero2, false
			}
		} else {
			selected, recv_val, ok := ch1.TryReceive(false)
			if selected {
				return 0, recv_val, zero2, ok
			}
		}

		// Try case 2
		if dir2 == SelectSend {
			if ch2.TrySend(val2, false) {
				return 1, zero1, zero2, false
			}
		} else {
			selected, recv_val, ok := ch2.TryReceive(false)
			if selected {
				return 1, zero1, recv_val, ok
			}
		}
	} else {
		// Try case 2 first
		if dir2 == SelectSend {
			if ch2.TrySend(val2, false) {
				return 1, zero1, zero2, false
			}
		} else {
			selected, recv_val, ok := ch2.TryReceive(false)
			if selected {
				return 1, zero1, recv_val, ok
			}
		}

		// Try case 1
		if dir1 == SelectSend {
			if ch1.TrySend(val1, false) {
				return 0, zero1, zero2, false
			}
		} else {
			selected, recv_val, ok := ch1.TryReceive(false)
			if selected {
				return 0, recv_val, zero2, ok
			}
		}
	}

	// Nothing selected
	return 2, zero1, zero2, false
}

func BlockingSelect3[T1, T2, T3 any](
	ch1 *Channel[T1], dir1 SelectDir, val1 T1,
	ch2 *Channel[T2], dir2 SelectDir, val2 T2,
	ch3 *Channel[T3], dir3 SelectDir, val3 T3) (uint64, T1, T2, T3, bool) {
	var zero1 T1
	var zero2 T2
	var zero3 T3
	for {
		// Randomly pick one of 3 cases
		r := primitive.RandomUint64() % 3
		if r == 0 {
			// Try case 1
			if dir1 == SelectSend {
				if ch1.TrySend(val1, true) {
					return 0, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch1.TryReceive(true)
				if selected {
					return 0, recv_val, zero2, zero3, ok
				}
			}
		} else if r == 1 {
			// Try case 2
			if dir2 == SelectSend {
				if ch2.TrySend(val2, true) {
					return 1, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch2.TryReceive(true)
				if selected {
					return 1, zero1, recv_val, zero3, ok
				}
			}
		} else {
			// Try case 3
			if dir3 == SelectSend {
				if ch3.TrySend(val3, true) {
					return 2, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch3.TryReceive(true)
				if selected {
					return 2, zero1, zero2, recv_val, ok
				}
			}
		}
	}
}

// Non-blocking select with 3 cases
// Returns (caseIndex, received_value1, received_value2, received_value3, ok)
// caseIndex = 3 means no selection
func NonBlockingSelect3[T1, T2, T3 any](
	ch1 *Channel[T1], dir1 SelectDir, val1 T1,
	ch2 *Channel[T2], dir2 SelectDir, val2 T2,
	ch3 *Channel[T3], dir3 SelectDir, val3 T3) (uint64, T1, T2, T3, bool) {
	var zero1 T1
	var zero2 T2
	var zero3 T3

	// Start with a random case
	start := primitive.RandomUint64() % 3

	// Try all 3 cases starting from the random one
	for i := uint64(0); i < 3; i++ {
		caseIdx := (start + i) % 3

		if caseIdx == 0 {
			if dir1 == SelectSend {
				if ch1.TrySend(val1, false) {
					return 0, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch1.TryReceive(false)
				if selected {
					return 0, recv_val, zero2, zero3, ok
				}
			}
		} else if caseIdx == 1 {
			if dir2 == SelectSend {
				if ch2.TrySend(val2, false) {
					return 1, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch2.TryReceive(false)
				if selected {
					return 1, zero1, recv_val, zero3, ok
				}
			}
		} else { // caseIdx == 2
			if dir3 == SelectSend {
				if ch3.TrySend(val3, false) {
					return 2, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch3.TryReceive(false)
				if selected {
					return 2, zero1, zero2, recv_val, ok
				}
			}
		}
	}

	// Nothing selected
	return 3, zero1, zero2, zero3, false
}
