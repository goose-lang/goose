package channel

import (
	"sync"

	"github.com/goose-lang/std/std_core"
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

	// Value only used for unbuffered channels
	v T
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

	// Create a send case for this channel
	sendCase := NewSendCase(c, val)

	// Run a blocking select with just this one case
	// This will block until the send succeeds
	Select1(sendCase, true)
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

	// Create a receive case for this channel
	recvCase := NewRecvCase(c)

	// Run a blocking select with just this one case
	// This will block until the receive succeeds
	Select1(recvCase, true)

	return recvCase.Value, recvCase.Ok
}

// This is a non-blocking attempt at closing. The only reason close blocks ever is because there
// may be successful exchanges that need to complete, which is equivalent to the go runtime where
// the closer must still obtain the channel's lock
func (c *Channel[T]) TryClose() bool {
	if c.state == closed {
		panic("close of closed channel")
	}
	// For unbuffered channels, if there is an exchange in progress, let the exchange complete.
	// In the real channel code the lock is held while this happens.
	if c.state != receiver_done && c.state != sender_done {
		c.state = closed
		return true
	}
	return false
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
	var done bool = false
	for !done {
		c.lock.Lock()
		done = c.TryClose()
		c.lock.Unlock()
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

// If there is a value available in the buffer, consume it, otherwise, don't select.
func (c *Channel[T]) BufferedTryReceiveLocked() (bool, T, bool) {
	var v T
	if c.count > 0 {
		v = c.buffer[c.first]
		c.first = (c.first + 1) % uint64(len(c.buffer))
		c.count -= 1
		return true, v, true
	}
	if c.state == closed {
		return true, v, false
	}
	return false, v, true
}

func (c *Channel[T]) BufferedTryReceive() (bool, T, bool) {
	c.lock.Lock()
	selected, return_val, ok := c.BufferedTryReceiveLocked()
	c.lock.Unlock()
	return selected, return_val, ok
}

type ReceiverState uint64

const (
	ReceiverCompletedWithSender ReceiverState = 0 // Receiver found a waiting sender
	ReceiverMadeOffer           ReceiverState = 1 // Receiver made an offer (no sender waiting)
	ReceiverObservedClosed      ReceiverState = 2 // Receiver saw that the channel was closed
	ReceiverCannotProceed       ReceiverState = 3 // Invalid state for receiving
)

func (c *Channel[T]) ReceiverCompleteOrOffer() ReceiverState {
	// A receiver is waiting, complete exchange
	if c.state == sender_ready {
		c.state = receiver_done
		return ReceiverCompletedWithSender
	}
	// No exchange in progress, make an offer, which will "lock" the channel from other
	// receivers since they will do nothing in this function if receiver_ready is observed.
	if c.state == start {
		c.state = receiver_ready
		return ReceiverMadeOffer
	}
	// Closed, we will return ok=false.
	if c.state == closed {
		return ReceiverObservedClosed
	}
	// An exchange is in progress, don't select.
	return ReceiverCannotProceed
}

type OfferResult uint64

const (
	OfferRescinded        OfferResult = 0 // Offer was rescinded (other party didn't arrive in time)
	CompletedExchange     OfferResult = 1 // Other party responded to our offer
	CloseInterruptedOffer OfferResult = 2 // Unexpected state, indicates model bugs.
)

func (c *Channel[T]) ReceiverCompleteOrRescindOffer() OfferResult {
	// Offer cancelled by close
	if c.state == closed {
		return CloseInterruptedOffer
	}
	// Offer wasn't accepted in time, rescind it.
	if c.state == receiver_ready {
		c.state = start
		return OfferRescinded
	}
	// Offer was accepted, complete the exchange.
	if c.state == sender_done {
		c.state = start
		return CompletedExchange
	}
	panic("Invalid state transition with open receive offer")
}

func (c *Channel[T]) UnbufferedTryReceive() (bool, T, bool) {
	var local_val T
	// First critical section: determine state and get value if sender is ready
	c.lock.Lock()
	try_select := c.ReceiverCompleteOrOffer()
	// Are we closed?
	var ok bool = !(try_select == ReceiverObservedClosed)
	// Closed and other party ready are selectable
	var selected bool = (try_select == ReceiverCompletedWithSender || !ok)
	if selected {
		// Save the value
		local_val = c.v
	}
	c.lock.Unlock()

	// If we offered, see if it was accepted
	if try_select == ReceiverMadeOffer {
		c.lock.Lock()
		offer_result := c.ReceiverCompleteOrRescindOffer()
		if offer_result == CompletedExchange {
			// Save and select if we managed to bait a sender.
			local_val = c.v
			selected = true
		}
		c.lock.Unlock()
	}

	return selected, local_val, ok
}

// Non-blocking receive function used for select statements. Blocking receive is modeled as
// a single blocking select statement which amounts to a for loop until selected.
func (c *Channel[T]) TryReceive() (bool, T, bool) {
	if uint64(len(c.buffer)) > 0 {
		return c.BufferedTryReceive()
	} else {
		return c.UnbufferedTryReceive()
	}
}

type SenderState uint64

const (
	SenderCompletedWithReceiver SenderState = 0 // Sender found a waiting receiver
	SenderMadeOffer             SenderState = 1 // Sender made an offer (no receiver waiting)
	SenderCannotProceed         SenderState = 2 // Exchange in progress, don't select
)

func (c *Channel[T]) SenderCompleteOrOffer(val T) SenderState {
	if c.state == closed {
		panic("send on closed channel")
	}
	// Receiver waiting, complete exchange.
	if c.state == receiver_ready {
		c.state = sender_done
		c.v = val
		return SenderCompletedWithReceiver
	}
	// No exchange in progress, make an offer.
	if c.state == start {
		c.state = sender_ready
		// Save the value in case the receiver completes the exchange.
		c.v = val
		return SenderMadeOffer
	}
	// Exchange in progress, don't select.
	return SenderCannotProceed
}

func (c *Channel[T]) SenderCheckOfferResult() OfferResult {
	if c.state == closed {
		panic("send on closed channel")
	}
	// Receiver accepted offer, complete exchange.
	if c.state == receiver_done {
		c.state = start
		return CompletedExchange
	}
	// Offer still stands, rescind it.
	if c.state == sender_ready {
		c.state = start
		return OfferRescinded
	}
	panic("Invalid state transition with open receive offer")
}

// If the buffer has free space, push our value.
func (c *Channel[T]) BufferedTrySend(val T) bool {
	if c.state == closed {
		panic("send on closed channel")
	}

	// If we have room, buffer our value
	if c.count < uint64(len(c.buffer)) {
		var last uint64 = (c.first + c.count) % uint64(len(c.buffer))
		c.buffer[last] = val
		c.count += 1
		return true
	}
	return false
}

// Non-Blocking send operation for select statements. Blocking send and blocking select
// statements simply call this in a for loop until it returns true.
func (c *Channel[T]) TrySend(val T) bool {
	var buffer_size uint64 = uint64(len(c.buffer))

	// Buffered channel:
	if buffer_size != 0 {
		c.lock.Lock()
		sendResult := c.BufferedTrySend(val)
		c.lock.Unlock()
		return sendResult
	}

	// Unbuffered channel:
	// First critical section: Try to complete send or make offer
	c.lock.Lock()
	senderState := c.SenderCompleteOrOffer(val)
	c.lock.Unlock()

	// Second critical section: Handle offer case if needed
	if senderState == SenderMadeOffer {
		c.lock.Lock()
		offerResult := c.SenderCheckOfferResult()
		c.lock.Unlock()
		return offerResult == CompletedExchange
	}

	// If we didn't make an offer, we either selected or an exchange is in progress so we bail.
	return senderState == SenderCompletedWithReceiver
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

// TrySelectAt attempts to select a specific case
func TrySelectAt[T any](selectCase *SelectCase[T]) bool {
	// nil is not selectable
	if selectCase.channel != nil {
		return TrySelect(selectCase)
	}
	return false
}

// TrySelectCase attempts to select a specific case at a given index
// Returns true if the case was selected, false otherwise
func TrySelectCase[T1, T2, T3, T4, T5 any](
	index uint64,
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4],
	case5 *SelectCase[T5]) bool {

	if index == 0 {
		return TrySelectAt(case1)
	}
	if index == 1 {
		return TrySelectAt(case2)
	}
	if index == 2 {
		return TrySelectAt(case3)
	}
	if index == 3 {
		return TrySelectAt(case4)
	}
	if index == 4 {
		return TrySelectAt(case5)
	}
	return false
}

// I want a value for representing the default case but I can't use -1 with uint64
// and I don't want this to be confused for a bug, so doing this.
const (
	DefaultCase uint64 = 5 // The value representing the default case
)

// TryCasesInOrder attempts to select one of the cases in the given order
// Returns the index of the selected case, or 5 if none was selected.
// I would probably return a sentinel value of 1 here but we are limited to
// uint64 and the index after the last makes sense since that would be where the
// default block is.
func TryCasesInOrder[T1, T2, T3, T4, T5 any](
	order []uint64,
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4],
	case5 *SelectCase[T5]) uint64 {
	var select_case uint64 = uint64(len(order))
	for _, i := range order {
		if select_case == uint64(len(order)) && TrySelectCase(i, case1, case2, case3, case4, case5) {
			select_case = uint64(i)
		}
	}
	return select_case
}

// MultiSelect performs a select operation on up to 5 cases.
// This is the largest number of cases the model will support, at least for now.
// Because of the fact that nil channels are not selectable, we can simply make
// this function never select a case with a nil channel and take advantage of
// this behavior to model selects with fewer than 5 statements by simply passing
// in "empty cases" that have a nil channel. This will allow verifying only the
// 5 statement case with a thin wrapper for the smaller ones.
//
// Cases with nil channels are ignored.
// This function returns the index of the selected case.
// If blocking is true, keep trying to select until a select succeeds.
// If blocking is false, return 5. 5 is the equivalent of a default case
// in Go channels.
func multiSelect[T1, T2, T3, T4, T5 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4],
	case5 *SelectCase[T5],
	blocking bool) uint64 {

	var selected_case uint64 = DefaultCase

	// Get a random order for fairness (only once, outside the loop)
	order := std_core.Permutation(5)

	// If nothing was selected and we're blocking, try in a loop
	for {
		selected_case = TryCasesInOrder(order, case1, case2, case3, case4, case5)
		if selected_case != DefaultCase || !blocking {
			break
		}
	}
	return selected_case
}

// Select1 performs a select operation on 1 case. This is used for Send and
// Receive as well, since these channel operations in Go are equivalent to
// a single case select statement with no default.
func Select1[T1 any](
	case1 *SelectCase[T1],
	blocking bool) uint64 {

	// Create empty cases with nil channels for the unused slots
	emptyCase2 := &SelectCase[uint64]{channel: nil}
	emptyCase3 := &SelectCase[uint64]{channel: nil}
	emptyCase4 := &SelectCase[uint64]{channel: nil}
	emptyCase5 := &SelectCase[uint64]{channel: nil}

	return multiSelect(
		case1,
		emptyCase2,
		emptyCase3,
		emptyCase4,
		emptyCase5,
		blocking)
}

// Select2 performs a select operation on 2 cases.
func Select2[T1, T2 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	blocking bool) uint64 {

	// Create empty cases with nil channels for the unused slots
	emptyCase3 := &SelectCase[uint64]{}
	emptyCase4 := &SelectCase[uint64]{}
	emptyCase5 := &SelectCase[uint64]{}

	return multiSelect(
		case1,
		case2,
		emptyCase3,
		emptyCase4,
		emptyCase5,
		blocking)
}

// Select3 performs a select operation on 3 cases.
func Select3[T1, T2, T3 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	blocking bool) uint64 {

	// Create empty cases with nil channels for the unused slots
	emptyCase4 := &SelectCase[uint64]{}
	emptyCase5 := &SelectCase[uint64]{}

	return multiSelect(
		case1,
		case2,
		case3,
		emptyCase4,
		emptyCase5,
		blocking)
}

// Select4 performs a select operation on 4 cases.
func Select4[T1, T2, T3, T4 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4],
	blocking bool) uint64 {

	// Create an empty case with nil channel for the unused slot
	emptyCase5 := &SelectCase[uint64]{}

	return multiSelect(
		case1,
		case2,
		case3,
		case4,
		emptyCase5,
		blocking)
}

// Select5 is just an alias to MultiSelect for consistency in the API.
func Select5[T1, T2, T3, T4, T5 any](
	case1 *SelectCase[T1],
	case2 *SelectCase[T2],
	case3 *SelectCase[T3],
	case4 *SelectCase[T4],
	case5 *SelectCase[T5],
	blocking bool) uint64 {

	return multiSelect(
		case1,
		case2,
		case3,
		case4,
		case5,
		blocking)
}

// Uses the applicable Try<Operation> function on the select case's channel. Default is always
// selectable so simply returns true.
func TrySelect[T any](select_case *SelectCase[T]) bool {
	var channel *Channel[T] = select_case.channel
	if channel == nil {
		return false
	}
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
	return false
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
