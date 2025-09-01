package channel

import (
	"sync"

	"github.com/goose-lang/primitive"
)

type OfferState uint64

const (
	Buffered OfferState = 0
	Idle     OfferState = 1
	SndWait  OfferState = 2
	RcvWait  OfferState = 3
	SndDone  OfferState = 4
	RcvDone  OfferState = 5
	Closed   OfferState = 6
)

type Channel[T any] struct {
	lock  *sync.Mutex
	state OfferState

	buffer []T
	cap    uint64

	// Value only used for unbuffered channels
	v T
}

// buffer_size = 0 is an unbuffered channel
func NewChannelRef[T any](buffer_size uint64) *Channel[T] {
	local_state := Idle
	if buffer_size > 0 {
		local_state = Buffered
	}
	return &Channel[T]{
		buffer: make([]T, 0),
		lock:   new(sync.Mutex),
		cap:    buffer_size,
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
func (c *Channel[T]) TryClose() bool {
	c.lock.Lock()
	switch c.state {
	case Closed:
		panic("close of closed channel")
	case Idle, Buffered:
		c.state = Closed
		c.lock.Unlock()
		return true
	// For unbuffered channels, if there is an exchange in progress, let the exchange complete.
	// In the runtime channel code the lock is held while this happens.
	default:
		c.lock.Unlock()
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
	for !c.TryClose() {
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

// Non-blocking receive function used for select statements.
// The blocking parameter here is used to determine whether or not we will make an offer to a
// waiting sender. If true, we will make an offer since blocking receive is modeled as a for loop
// around nonblocking TryReceive. If false, we don't make an offer since we don't need to match
// with another non-blocking send.
func (c *Channel[T]) TryReceive(blocking bool) (bool, T, bool) {
	var local_val T
	// First critical section: determine state and get value if sender is ready
	c.lock.Lock()
	switch c.state {
	case Buffered:
		var v T
		if len(c.buffer) > 0 {
			val_copy := c.buffer[0]
			c.buffer = c.buffer[1:]
			c.lock.Unlock()
			return true, val_copy, true
		}
		c.lock.Unlock()
		return false, v, true
	case Closed:
		// For a buffered channel, we drain the buffer before returning ok=false.
		if len(c.buffer) > 0 {
			val_copy := c.buffer[0]
			c.buffer = c.buffer[1:]
			c.lock.Unlock()
			return true, val_copy, true
		}
		c.lock.Unlock()
		return true, local_val, false
	// Sender is making an offer, accept it
	case SndWait:
		local_val = c.v
		c.state = RcvDone
		c.lock.Unlock()
		return true, local_val, true
	case Idle:
		if blocking {
			c.state = RcvWait
			c.lock.Unlock()
			c.lock.Lock()
			switch c.state {
			// Offer wasn't accepted in time, rescind it.
			case RcvWait:
				c.state = Idle
				c.lock.Unlock()
				return false, local_val, true
			// Offer was accepted, reset channel.
			case SndDone:
				c.state = Idle
				local_val = c.v
				c.lock.Unlock()
				return true, local_val, true
			default:
				// The protocol does not allow interference when an offer is outgoing.
				panic("not supposed to be here!")
			}
		}
		// For nonblocking, we can't make offers, only can complete them.
		c.lock.Unlock()
		return false, local_val, true
	// An exchange is in progress that we can't participate in.
	default:
		c.lock.Unlock()
		return false, local_val, true
	}
}

// Non-Blocking send operation for select statements. Blocking send and blocking select
// statements simply call this in a for loop until it returns true.
func (c *Channel[T]) TrySend(val T, blocking bool) bool {
	c.lock.Lock()
	switch c.state {
	case Closed:
		panic("send on closed channel")
	case Buffered:
		// If we have room, buffer our value
		if len(c.buffer) < int(c.cap) {
			c.buffer = append(c.buffer, val)
			c.lock.Unlock()
			return true
		}
		c.lock.Unlock()
		return false
	case RcvWait:
		// Receiver offers, accept offer.
		c.state = SndDone
		c.v = val
		c.lock.Unlock()
		return true
	case Idle:
		// Make an offer only if blocking.
		if blocking {
			c.state = SndWait
			// Save the value in case the receiver completes the exchange.
			c.v = val
			c.lock.Unlock()
			c.lock.Lock()
			switch c.state {
			// Receiver accepts, reset the channel.
			case RcvDone:
				c.state = Idle
				c.lock.Unlock()
				return true
			// Offer still stands, rescind it.
			case SndWait:
				c.state = Idle
				c.lock.Unlock()
				return false
			// This protocol doesn't work if other parties can cancel the exchange.
			default:
				panic("Invalid state transition with open receive offer")
			}
		}
		// Nonblocking sends can't make offers, only can accept them.
		c.lock.Unlock()
		return false
	// An exchange is in progress that we can't participate in.
	default:
		c.lock.Unlock()
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
func (c *Channel[T]) Len() uint64 {
	if c == nil {
		return 0
	}
	var chan_len uint64 = 0
	c.lock.Lock()
	chan_len = uint64(len(c.buffer))
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
	return c.cap
}

// The code below models select statements in a similar way to the reflect package's
// dynamic select statements. See unit tests in channel_test.go for examples of
// the intended translation.
type SelectDir uint64

const (
	SelectSend SelectDir = 0 // case Chan <- Send
	SelectRecv SelectDir = 1 // case <-Chan:
)

// value is used for the value the sender will send and also used to return the received value by
// reference.
type SelectCase[T any] struct {
	channel *Channel[T]
	dir     SelectDir
	Value   T
	Ok      bool
}

func NewSendCase[T any](channel *Channel[T], value T) *SelectCase[T] {
	return &SelectCase[T]{
		channel: channel,
		dir:     SelectSend,
		Value:   value,
	}
}

func NewRecvCase[T any](channel *Channel[T]) *SelectCase[T] {
	return &SelectCase[T]{
		channel: channel,
		dir:     SelectRecv,
	}
}

// Uses the applicable Try<Operation> function on the select case's channel. Default is always
// selectable so simply returns true.
func TrySelect[T any](select_case *SelectCase[T], blocking bool) bool {
	var channel *Channel[T] = select_case.channel
	if channel == nil {
		return false
	}
	if select_case.dir == SelectSend {
		return channel.TrySend(select_case.Value, blocking)
	}
	if select_case.dir == SelectRecv {
		var item T
		var ok bool
		var selected bool
		selected, item, ok = channel.TryReceive(blocking)
		// We can use these values for return by reference and they will be implicitly kept alive
		// by the garbage collector so we can use value here for both the send and receive
		// variants. What a miracle it is to not be using C++.
		select_case.Value = item
		select_case.Ok = ok
		return selected

	}
	return false
}

// Select1 performs a select operation on 1 case. This is used for Send and
// Receive as well, since these channel operations in Go are equivalent to
// a single case select statement with no default.
func Select1[T1 any](
	case1 *SelectCase[T1],
	blocking bool) bool {
	var selected bool
	for {
		selected = TrySelect(case1, blocking)
		if selected || !blocking {
			break
		}
	}
	return selected
}

func TrySelectCase2[T1, T2 any](
	index uint64,
	case1 *SelectCase[T1],
	case2 *SelectCase[T2], blocking bool) bool {
	if index == 0 {
		return TrySelect(case1, blocking)
	}
	if index == 1 {
		return TrySelect(case2, blocking)
	}
	panic("index needs to be 0 or 1")
}

func Select2[T1, T2 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	blocking bool) uint64 {

	i := primitive.RandomUint64() % uint64(2)
	if TrySelectCase2(i, case1, case2, blocking) {
		return i
	}

	// If nothing was selected and we're blocking, try in a loop
	for {
		if TrySelect(case1, blocking) {
			return 0
		}
		if TrySelect(case2, blocking) {
			return 1
		}
		if !blocking {
			return 2
		}
	}
}

func TrySelectCase3[T1, T2, T3 any](
	index uint64,
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3], blocking bool) bool {
	if index == 0 {
		return TrySelect(case1, blocking)
	}
	if index == 1 {
		return TrySelect(case2, blocking)
	}
	if index == 2 {
		return TrySelect(case3, blocking)
	}
	panic("index needs to be 0, 1 or 2")
}

func Select3[T1, T2, T3 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	blocking bool) uint64 {

	i := primitive.RandomUint64() % uint64(3)
	if TrySelectCase3(i, case1, case2, case3, blocking) {
		return i
	}

	for {
		if TrySelect(case1, blocking) {
			return 0
		}
		if TrySelect(case2, blocking) {
			return 1
		}
		if TrySelect(case3, blocking) {
			return 2
		}
		if !blocking {
			return 3
		}
	}
}

func TrySelectCase4[T1, T2, T3, T4 any](
	index uint64,
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4], blocking bool) bool {
	if index == 0 {
		return TrySelect(case1, blocking)
	}
	if index == 1 {
		return TrySelect(case2, blocking)
	}
	if index == 2 {
		return TrySelect(case3, blocking)
	}
	if index == 3 {
		return TrySelect(case4, blocking)
	}
	panic("index needs to be 0, 1, 2 or 3")
}

func Select4[T1, T2, T3, T4 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4],
	blocking bool) uint64 {

	i := primitive.RandomUint64() % uint64(4)
	if TrySelectCase4(i, case1, case2, case3, case4, blocking) {
		return i
	}

	for {
		if TrySelect(case1, blocking) {
			return 0
		}
		if TrySelect(case2, blocking) {
			return 1
		}
		if TrySelect(case3, blocking) {
			return 2
		}
		if TrySelect(case4, blocking) {
			return 3
		}
		if !blocking {
			return 4
		}
	}
}

func TrySelectCase5[T1, T2, T3, T4, T5 any](
	index uint64,
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4],
	case5 *SelectCase[T5], blocking bool) bool {
	if index == 0 {
		return TrySelect(case1, blocking)
	}
	if index == 1 {
		return TrySelect(case2, blocking)
	}
	if index == 2 {
		return TrySelect(case3, blocking)
	}
	if index == 3 {
		return TrySelect(case4, blocking)
	}
	if index == 4 {
		return TrySelect(case5, blocking)
	}
	panic("index needs to be 0, 1, 2, 3 or 4")
}

func Select5[T1, T2, T3, T4, T5 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4],
	case5 *SelectCase[T5],
	blocking bool) uint64 {

	i := primitive.RandomUint64() % uint64(5)
	if TrySelectCase5(i, case1, case2, case3, case4, case5, blocking) {
		return i
	}

	for {
		if TrySelect(case1, blocking) {
			return 0
		}
		if TrySelect(case2, blocking) {
			return 1
		}
		if TrySelect(case3, blocking) {
			return 2
		}
		if TrySelect(case4, blocking) {
			return 3
		}
		if TrySelect(case5, blocking) {
			return 4
		}
		if !blocking {
			return 5
		}
	}
}
