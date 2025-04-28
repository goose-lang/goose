package channel_test

/*
Tests to demonstrate Go's behavior on various subtle examples.
*/

import (
	"fmt"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/goose-lang/goose/channel"
)

// The channel tests below are for the Goose model of channels that is implemented as a Go
// struct. The tests are hand translated versions of correctness based tests in
// https://go.dev/src/runtime/chan_test.go https://go.dev/src/runtime/chanbarrier_test.go
func TestChan(t *testing.T) {
	defer runtime.GOMAXPROCS(runtime.GOMAXPROCS(4))
	var N uint64 = 200
	if testing.Short() {
		N = 20
	}
	for chanCap := uint64(0); chanCap < N; chanCap++ {
		{
			// Ensure that receive from empty chan blocks.
			c := channel.NewChannelRef[uint64](chanCap)
			recv1 := false
			go func() {
				_, _ = c.Receive()
				recv1 = true
			}()
			recv2 := false
			go func() {
				_, _ = c.Receive()
				recv2 = true
			}()
			time.Sleep(time.Millisecond)
			if recv1 || recv2 {
				t.Fatalf("chan[%d]: receive from empty chan", chanCap)
			}
			// Ensure that non-blocking receive does not block.

			selected, _, _ := c.TryReceive()
			if selected {
				t.Fatalf("chan[%d]: receive from empty chan", chanCap)
			}

			selected, _, _ = c.TryReceive()
			if selected {
				t.Fatalf("chan[%d]: receive from empty chan", chanCap)
			}
			c.Send(0)
			c.Send(0)
		}

		{
			// Ensure that send to full chan blocks.
			c := channel.NewChannelRef[uint64](chanCap)
			for i := uint64(0); i < chanCap; i++ {
				c.Send(i)
			}
			sent := uint32(0)
			go func() {
				c.Send(0)
				atomic.StoreUint32(&sent, 1)
			}()
			time.Sleep(time.Millisecond)
			if atomic.LoadUint32(&sent) != 0 {
				t.Fatalf("chan[%d]: send to full chan", chanCap)
			}
			selected := c.TrySend(0)
			if selected {
				t.Fatalf("chan[%d]: send to full chan", chanCap)
			}
			c.Receive()
		}

		{
			// Ensure that we receive 0 from closed chan.
			c := channel.NewChannelRef[uint64](chanCap)
			for i := uint64(0); i < chanCap; i++ {
				c.Send(i)
			}
			c.Close()
			for i := uint64(0); i < chanCap; i++ {
				v, _ := c.Receive()
				if v != i {
					t.Fatalf("chan[%d]: received %v, expected %v", chanCap, v, i)
				}
			}
			if v, _ := c.Receive(); v != 0 {
				t.Fatalf("chan[%d]: received %v, expected %v", chanCap, v, 0)
			}
			if v, ok := c.Receive(); v != 0 || ok {
				t.Fatalf("chan[%d]: received %v/%v, expected %v/%v", chanCap, v, ok, 0, false)
			}
		}

		{
			// Ensure that close unblocks receive.
			c := channel.NewChannelRef[uint64](chanCap)
			done := channel.NewChannelRef[bool](0)
			go func() {
				v, ok := c.Receive()
				done.Send(v == 0 && ok == false)
			}()
			time.Sleep(time.Millisecond)
			c.Close()
			actually_done, _ := done.Receive()
			if !actually_done {
				t.Fatalf("chan[%d]: received non zero from closed chan", chanCap)
			}
		}

		{
			// Send 100 integers,
			// ensure that we receive them non-corrupted in FIFO order.
			c := channel.NewChannelRef[uint64](chanCap)
			go func() {
				for i := uint64(0); i < 100; i++ {
					c.Send(i)
				}
			}()
			for i := uint64(0); i < 100; i++ {
				v, _ := c.Receive()
				if v != i {
					t.Fatalf("chan[%d]: received %v, expected %v", chanCap, v, i)
				}
			}

			// Same, but using recv2.
			go func() {
				for i := uint64(0); i < 100; i++ {
					c.Send(i)
				}
			}()
			for i := uint64(0); i < 100; i++ {
				v, ok := c.Receive()
				if !ok {
					t.Fatalf("chan[%d]: receive failed, expected %v", chanCap, i)
				}
				if v != i {
					t.Fatalf("chan[%d]: received %v, expected %v", chanCap, v, i)
				}
			}

			// Send 1000 integers in 4 goroutines,
			// ensure that we receive what we send.
			const P = 4
			const L uint64 = 1000
			for p := 0; p < P; p++ {
				go func() {
					for i := uint64(0); i < L; i++ {
						c.Send(i)
					}
				}()
			}
			done := channel.NewChannelRef[map[uint64]uint64](chanCap)
			for p := uint64(0); p < P; p++ {
				go func() {
					recv := make(map[uint64]uint64)
					for i := uint64(0); i < L; i++ {
						v, _ := c.Receive()
						recv[v] = recv[v] + 1
					}
					done.Send(recv)
				}()
			}
			recv := make(map[uint64]uint64)
			for p := uint64(0); p < P; p++ {
				received_val, _ := done.Receive()
				for k, v := range received_val {
					recv[k] = recv[k] + v
				}
			}
			if uint64(len(recv)) != L {
				t.Fatalf("chan[%d]: received %v values, expected %v", chanCap, len(recv), L)
			}
			for _, v := range recv {
				if v != P {
					t.Fatalf("chan[%d]: received %v values, expected %v", chanCap, v, P)
				}
			}
		}

		{
			// Test len/cap.
			c := channel.NewChannelRef[uint64](chanCap)
			if c.Len() != uint64(0) || c.Cap() != chanCap {
				t.Fatalf("chan[%d]: bad len/cap, expect %v/%v, got %v/%v", chanCap, 0, chanCap, c.Len(), c.Cap())
			}
			for i := uint64(0); i < chanCap; i++ {
				c.Send(i)
			}
			if c.Len() != chanCap || c.Cap() != chanCap {
				t.Fatalf("chan[%d]: bad len/cap, expect %v/%v, got %v/%v", chanCap, chanCap, chanCap, c.Len(), c.Cap())
			}
		}
	}
}

// This just makes sure that we have the same semantics for len and cap. I don't
// think we plan on doing much with these, but if we do, might as well get it right
func TestLenCapComparedWithGoChannels(t *testing.T) {
	capacities := []uint64{0, 1, 2, 5, 10}

	for _, capacity := range capacities {
		t.Run(fmt.Sprintf("Capacity%d", capacity), func(t *testing.T) {
			// Create both channel types
			goChan := make(chan int, capacity)
			ourChan := channel.NewChannelRef[int](capacity)

			// Test initial state
			goLen := len(goChan)
			goCap := cap(goChan)
			ourLen := int(ourChan.Len())
			ourCap := int(ourChan.Cap())

			if goLen != ourLen || goCap != ourCap {
				t.Errorf("Initial state mismatch: Go len/cap: %d/%d, Our len/cap: %d/%d",
					goLen, goCap, ourLen, ourCap)
			}

			// Test after adding items
			itemsToAdd := capacity
			if capacity == 0 {
				itemsToAdd = 0
			} else {
				for i := uint64(0); i < capacity; i++ {
					goChan <- int(i)
					ourChan.Send(int(i))
				}

				goLen = len(goChan)
				goCap = cap(goChan)
				ourLen = int(ourChan.Len())
				ourCap = int(ourChan.Cap())

				if goLen != ourLen || goCap != ourCap {
					t.Errorf("After filling mismatch: Go len/cap: %d/%d, Our len/cap: %d/%d",
						goLen, goCap, ourLen, ourCap)
				}
			}

			// Test after removing half the items
			if itemsToAdd > 0 {
				itemsToRemove := itemsToAdd / 2
				for i := uint64(0); i < itemsToRemove; i++ {
					<-goChan
					ourChan.Receive()
				}

				goLen = len(goChan)
				goCap = cap(goChan)
				ourLen = int(ourChan.Len())
				ourCap = int(ourChan.Cap())

				if goLen != ourLen || goCap != ourCap {
					t.Errorf("After partial removal mismatch: Go len/cap: %d/%d, Our len/cap: %d/%d",
						goLen, goCap, ourLen, ourCap)
				}
			}

			// Test after closing
			// Need to drain remaining items first to compare fairly
			if itemsToAdd > 0 {
				remainingItems := itemsToAdd - (itemsToAdd / 2)
				for i := uint64(0); i < remainingItems; i++ {
					<-goChan
					ourChan.Receive()
				}
			}

			close(goChan)
			ourChan.Close()

			goLen = len(goChan)
			goCap = cap(goChan)
			ourLen = int(ourChan.Len())
			ourCap = int(ourChan.Cap())

			if goLen != ourLen || goCap != ourCap {
				t.Errorf("After closing mismatch: Go len/cap: %d/%d, Our len/cap: %d/%d",
					goLen, goCap, ourLen, ourCap)
			}
		})
	}

	// Test special case: nil channel
	t.Run("NilChannel", func(t *testing.T) {
		var goChan chan int
		var ourChan *channel.Channel[int]

		goLen := len(goChan)
		goCap := cap(goChan)
		ourLen := int(ourChan.Len()) // Should return 0 for nil channel
		ourCap := int(ourChan.Cap()) // Should return 0 for nil channel

		if goLen != ourLen || goCap != ourCap {
			t.Errorf("Nil channel mismatch: Go len/cap: %d/%d, Our len/cap: %d/%d",
				goLen, goCap, ourLen, ourCap)
		}
	})
}

// Some extra dummy checks for blocking behavior. Nil blocking is checked as well
func TestBlockingBehavior(t *testing.T) {
	timeout := time.Second // Reasonable timeout to check blocking behavior

	t.Run("ReceiveFromEmptyBlocks", func(t *testing.T) {
		c := channel.NewChannelRef[int](0) // Unbuffered channel

		done := make(chan bool)
		go func() {
			_, _ = c.Receive() // This should block
			done <- true
		}()

		select {
		case <-done:
			t.Error("Receive from empty channel didn't block as expected")
		case <-time.After(timeout):
			// If we reach here, the operation blocked as expected
		}
	})

	t.Run("SendToFullBlocks", func(t *testing.T) {
		c := channel.NewChannelRef[int](1) // Buffered channel with capacity 1
		c.Send(42)                         // Fill the channel

		done := make(chan bool)
		go func() {
			c.Send(43) // This should block
			done <- true
		}()

		select {
		case <-done:
			t.Error("Send to full channel didn't block as expected")
		case <-time.After(timeout):
			// If we reach here, the operation blocked as expected
		}

		// Clean up
		_, _ = c.Receive()
		select {
		case <-done:
			// Expected - operation completes
		case <-time.After(timeout):
			t.Error("Send operation didn't complete after space became available")
		}
	})

	// Test nil channel behavior
	t.Run("NilChannelBlocks", func(t *testing.T) {
		// Test nil channel send
		t.Run("SendToNilBlocks", func(t *testing.T) {
			// Compare with Go's behavior
			var goChan chan int
			var ourChan *channel.Channel[int] = nil

			goBlocked := true
			ourBlocked := true

			// Test Go's behavior
			goBlockDone := make(chan bool)
			go func() {
				goChan <- 42 // This should block
				goBlockDone <- true
			}()

			// Test our implementation
			ourBlockDone := make(chan bool)
			go func() {
				ourChan.Send(42) // This should block
				ourBlockDone <- true
			}()

			// Check if both operations block
			select {
			case <-goBlockDone:
				goBlocked = false
				t.Error("Go's send to nil channel didn't block as expected")
			case <-ourBlockDone:
				ourBlocked = false
				t.Error("Our send to nil channel didn't block as expected")
			case <-time.After(timeout):
				// Both blocked, which is expected
			}

			if !goBlocked || !ourBlocked {
				t.Errorf("Nil channel send blocking behavior mismatch: Go blocked: %v, Our blocked: %v",
					goBlocked, ourBlocked)
			}
		})

		// Test nil channel receive
		t.Run("ReceiveFromNilBlocks", func(t *testing.T) {
			// Compare with Go's behavior
			var goChan chan int
			var ourChan *channel.Channel[int] = nil

			goBlocked := true
			ourBlocked := true

			// Test Go's behavior
			goBlockDone := make(chan bool)
			go func() {
				_ = <-goChan // This should block
				goBlockDone <- true
			}()

			// Test our implementation
			ourBlockDone := make(chan bool)
			go func() {
				_, _ = ourChan.Receive() // This should block
				ourBlockDone <- true
			}()

			// Check if both operations block
			select {
			case <-goBlockDone:
				goBlocked = false
				t.Error("Go's receive from nil channel didn't block as expected")
			case <-ourBlockDone:
				ourBlocked = false
				t.Error("Our receive from nil channel didn't block as expected")
			case <-time.After(timeout):
				// Both blocked, which is expected
			}

			if !goBlocked || !ourBlocked {
				t.Errorf("Nil channel receive blocking behavior mismatch: Go blocked: %v, Our blocked: %v",
					goBlocked, ourBlocked)
			}
		})
	})
}

// Make sure the panic situations lead to panic in the model with the same message.
func TestPanicComparedWithGoChannels(t *testing.T) {
	// Helper function to check if an operation panics and capture the panic message
	assertPanicsWithMessage := func(f func()) (didPanic bool, message string) {
		defer func() {
			if r := recover(); r != nil {
				didPanic = true
				message = fmt.Sprint(r)
			}
		}()
		f()
		return false, ""
	}

	// Test send on closed channel
	t.Run("SendOnClosedChannel", func(t *testing.T) {
		// Test with Go's native channel
		goChan := make(chan int, 1)
		close(goChan)
		goDidPanic, goMessage := assertPanicsWithMessage(func() {
			goChan <- 42
		})

		// Test with our channel implementation
		ourChan := channel.NewChannelRef[int](1)
		ourChan.Close()
		ourDidPanic, ourMessage := assertPanicsWithMessage(func() {
			ourChan.Send(42)
		})

		// Compare results
		if goDidPanic != ourDidPanic {
			t.Errorf("Behavior mismatch: Go channel panicked: %v, Our channel panicked: %v",
				goDidPanic, ourDidPanic)
		}

		// Compare error messages
		if goDidPanic && ourDidPanic {
			if !strings.Contains(ourMessage, "send on closed channel") {
				t.Errorf("Error message mismatch:\nGo message: %q\nOur message: %q",
					goMessage, ourMessage)
			}
		}
	})

	// Test close on closed channel
	t.Run("CloseOnClosedChannel", func(t *testing.T) {
		// Test with Go's native channel
		goChan := make(chan int, 1)
		close(goChan)
		goDidPanic, goMessage := assertPanicsWithMessage(func() {
			close(goChan)
		})

		// Test with our channel implementation
		ourChan := channel.NewChannelRef[int](1)
		ourChan.Close()
		ourDidPanic, ourMessage := assertPanicsWithMessage(func() {
			ourChan.Close()
		})

		// Compare results
		if goDidPanic != ourDidPanic {
			t.Errorf("Behavior mismatch: Go channel panicked: %v, Our channel panicked: %v",
				goDidPanic, ourDidPanic)
		}

		// Compare error messages
		if goDidPanic && ourDidPanic {
			if !strings.Contains(ourMessage, "close of closed channel") {
				t.Errorf("Error message mismatch:\nGo message: %q\nOur message: %q",
					goMessage, ourMessage)
			}
		}
	})

	// Test try-send on closed channel (using select with default for Go)
	t.Run("TrySendOnClosedChannel", func(t *testing.T) {
		// Test with Go's native channel
		goChan := make(chan int, 1)
		close(goChan)
		goDidPanic, goMessage := assertPanicsWithMessage(func() {
			select {
			case goChan <- 42:
				// Should panic before reaching here
			default:
				// Should panic before reaching here
			}
		})

		// Test with our channel implementation
		ourChan := channel.NewChannelRef[int](1)
		ourChan.Close()
		ourDidPanic, ourMessage := assertPanicsWithMessage(func() {
			ourChan.TrySend(42)
		})

		// Compare results
		if goDidPanic != ourDidPanic {
			t.Errorf("Behavior mismatch: Go channel panicked: %v, Our channel panicked: %v",
				goDidPanic, ourDidPanic)
		}

		// Compare error messages
		if goDidPanic && ourDidPanic {
			if !strings.Contains(ourMessage, "send on closed channel") {
				t.Errorf("Error message mismatch:\nGo message: %q\nOur message: %q",
					goMessage, ourMessage)
			}
		}
	})

	// Test buffered try-send on closed channel
	t.Run("BufferedTrySendOnClosedChannel", func(t *testing.T) {
		// Test with Go's native channel
		goChan := make(chan int, 5)
		close(goChan)
		goDidPanic, goMessage := assertPanicsWithMessage(func() {
			select {
			case goChan <- 42:
				// Should panic before reaching here
			default:
				// Should panic before reaching here
			}
		})

		// Test with our channel implementation
		ourChan := channel.NewChannelRef[int](5)
		ourChan.Close()
		ourDidPanic, ourMessage := assertPanicsWithMessage(func() {
			ourChan.TrySend(42)
		})

		// Compare results
		if goDidPanic != ourDidPanic {
			t.Errorf("Behavior mismatch: Go channel panicked: %v, Our channel panicked: %v",
				goDidPanic, ourDidPanic)
		}

		// Compare error messages
		if goDidPanic && ourDidPanic {
			if !strings.Contains(ourMessage, "send on closed channel") {
				t.Errorf("Error message mismatch:\nGo message: %q\nOur message: %q",
					goMessage, ourMessage)
			}
		}
	})

	// Test close of nil channel
	t.Run("CloseNilChannel", func(t *testing.T) {
		// Test with Go's native channel
		var goChan chan int
		goDidPanic, goMessage := assertPanicsWithMessage(func() {
			close(goChan)
		})

		// Test with our channel implementation
		var ourChan *channel.Channel[int]
		ourDidPanic, ourMessage := assertPanicsWithMessage(func() {
			ourChan.Close()
		})

		// Compare results
		if goDidPanic != ourDidPanic {
			t.Errorf("Behavior mismatch: Go channel panicked: %v, Our channel panicked: %v",
				goDidPanic, ourDidPanic)
		}

		// Compare error messages
		if goDidPanic && ourDidPanic {
			if !strings.Contains(ourMessage, "close of nil channel") {
				t.Errorf("Error message mismatch:\nGo message: %q\nOur message: %q",
					goMessage, ourMessage)
			}
		}
	})
}

func TestNonblockRecvRace(t *testing.T) {
	var n uint64 = 10000
	if testing.Short() {
		n = 100
	}
	for i := uint64(0); i < n; i++ {
		c := channel.NewChannelRef[uint64](1)
		c.Send(1)
		go func() {
			selected, _, _ := c.TryReceive()
			if !selected {
				t.Error("chan is not ready")
			}
		}()
		c.Close()
		c.Receive()
		if t.Failed() {
			return
		}
	}
}
func TestMultiConsumer(t *testing.T) {
	const nwork uint64 = 23
	const niter uint64 = 271828

	pn := []uint64{2, 3, 7, 11, 13, 17, 19, 23, 27, 31}

	q := channel.NewChannelRef[uint64](nwork * 3)
	r := channel.NewChannelRef[uint64](nwork * 3)

	// workers
	var wg sync.WaitGroup
	for i := uint64(0); i < nwork; i++ {
		wg.Add(1)
		go func(w uint64) {
			for {
				selected, val, ok := q.TryReceive()
				if !ok {
					break
				}
				if selected {
					if pn[w%uint64(len(pn))] == val {
						runtime.Gosched()
					}
					r.Send(val)
				}
			}
			wg.Done()
		}(i)
	}

	// feeder & closer
	var expect uint64 = 0
	go func() {
		for i := uint64(0); i < niter; i++ {
			v := pn[i%uint64(len(pn))]
			expect += v
			q.Send(v)
		}
		q.Close() // no more work
		wg.Wait() // workers done
		r.Close() // ... so there can be no more results
	}()

	// consume & check
	var n uint64 = 0
	var s uint64 = 0
	for {
		selected, val, ok := r.TryReceive()
		if !ok {
			break
		}
		if selected {
			n++
			s += val
		}
	}
	if n != niter || s != expect {
		t.Errorf("Expected sum %d (got %d) from %d iter (saw %d)",
			expect, s, niter, n)
	}
}

type response struct {
}

type myError struct {
}

func (myError) Error() string { return "" }

func doRequest(useSelect bool) (*response, error) {
	type async struct {
		resp *response
		err  error
	}
	ch := channel.NewChannelRef[*async](0)
	done := channel.NewChannelRef[struct{}](0)

	if useSelect {
		go func() {
			case_1 := channel.NewSendCase(ch, &async{resp: nil, err: myError{}})
			case_2 := channel.NewRecvCase(done)
			selected_case := channel.TwoCaseSelect(&case_1, &case_2, true)
			// These cases don't actually do anything but wanted to stick with the intended
			// translation throughout this file.
			if selected_case == 0 {

			} else if selected_case == 1 {

			}
		}()
	} else {
		go func() {
			ch.Send(&async{resp: nil, err: myError{}})
		}()
	}

	var r *async = ch.ReceiveDiscardOk()
	runtime.Gosched()
	return r.resp, r.err
}

func TestChanSendSelectBarrier(t *testing.T) {
	t.Parallel()
	testChanSendBarrier(true)
}

func TestChanSendBarrier(t *testing.T) {
	t.Parallel()
	testChanSendBarrier(false)
}

func testChanSendBarrier(useSelect bool) {
	var wg sync.WaitGroup
	outer := 2
	inner := 20
	for i := 0; i < outer; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			var garbage []byte
			for j := 0; j < inner; j++ {
				_, err := doRequest(useSelect)
				_, ok := err.(myError)
				if !ok {
					panic(1)
				}
				garbage = makeByte()
			}
			_ = garbage
		}()
	}
	wg.Wait()
}

//go:noinline
func makeByte() []byte {
	return make([]byte, 1<<10)
}

// This test checks that select acts on the state of the channels at one
// moment in the execution, not over a smeared time window.
// In the test, one goroutine does:
//
//	create c1, c2
//	make c1 ready for receiving
//	create second goroutine
//	make c2 ready for receiving
//	make c1 no longer ready for receiving (if possible)
//
// The second goroutine does a non-blocking select receiving from c1 and c2.
// From the time the second goroutine is created, at least one of c1 and c2
// is always ready for receiving, so the select in the second goroutine must
// always receive from one or the other. It must never execute the default case.
func TestNonblockSelectRace(t *testing.T) {
	n := 100000
	if testing.Short() {
		n = 1000
	}
	done := channel.NewChannelRef[bool](0)
	for i := 0; i < n; i++ {
		c1 := channel.NewChannelRef[int](1)
		c2 := channel.NewChannelRef[int](1)
		c1.Send(1)
		go func() {
			case_1 := channel.NewRecvCase(c1)
			case_2 := channel.NewRecvCase(c2)
			selected_case := channel.TwoCaseSelect(&case_1, &case_2, false)
			if selected_case == 0 {
			}
			if selected_case == 1 {

			}
			if selected_case == 2 {
				done.Send(false)
				return
			}
			done.Send(true)
		}()
		c2.Send(1)
		c1.TryReceive()
		val := done.ReceiveDiscardOk()
		if !val {
			t.Fatal("no chan is ready")
		}
	}
}

// Same as TestNonblockSelectRace, but close(c2) replaces c2 <- 1.
func TestNonblockSelectRace2(t *testing.T) {
	n := 100000
	if testing.Short() {
		n = 1000
	}
	done := channel.NewChannelRef[bool](0)
	for i := 0; i < n; i++ {
		c1 := channel.NewChannelRef[int](1)
		c2 := channel.NewChannelRef[int](1)
		c1.Send(1)
		go func() {
			case_1 := channel.NewRecvCase(c1)
			case_2 := channel.NewRecvCase(c2)
			selected_case := channel.TwoCaseSelect(&case_1, &case_2, false)
			if selected_case == 0 {
			}
			if selected_case == 1 {

			}
			if selected_case == 2 {
				done.Send(false)
				return
			}
			done.Send(true)
		}()
		c2.Close()
		c1.TryReceive()
		val := done.ReceiveDiscardOk()
		if !val {
			t.Fatal("no chan is ready")
		}
	}
}

// Make sure that we can handle blocking select statements with matching send/receive
// operations.
func TestSelfSelect(t *testing.T) {
	// Ensure that send/recv on the same chan in select
	// does not crash nor deadlock.
	defer runtime.GOMAXPROCS(runtime.GOMAXPROCS(2))
	for _, chanCap := range []uint64{0, 10} {
		var wg sync.WaitGroup
		wg.Add(2)
		c := channel.NewChannelRef[uint64](uint64(chanCap))
		for p := uint64(0); p < 2; p++ {
			p := p
			go func() {
				defer wg.Done()
				for i := uint64(0); i < 1000; i++ {
					if p == 0 || i%2 == 0 {
						case_1 := channel.NewSendCase(c, p)
						case_2 := channel.NewRecvCase(c)
						selected_case := channel.TwoCaseSelect(&case_1, &case_2, true)
						if selected_case == 0 {
							break
						} else if selected_case == 1 {
							if chanCap == 0 && case_2.Value == p {
								t.Errorf("self receive")
								return
							}
							break
						}
					} else {
						case_1 := channel.NewRecvCase(c)
						case_2 := channel.NewSendCase(c, p)
						selected_case := channel.TwoCaseSelect(&case_1, &case_2, true)
						if selected_case == 0 {
							if chanCap == 0 && case_1.Value == p {
								t.Errorf("self receive")
								return
							}
							break
						} else if selected_case == 1 {
							break
						}
					}
				}
			}()
		}
		wg.Wait()
	}
}

// Make sure that a "perpetually selectable" closed receive case appearing first does not mean
// it will be selected every time.
func TestSelectLivenessOrder1(t *testing.T) {
	c1 := channel.NewChannelRef[uint64](uint64(0))
	c2 := channel.NewChannelRef[uint64](uint64(2))
	c1.Close()
	c2.Send(0)

	case_1 := channel.NewRecvCase(c1)
	case_2 := channel.NewRecvCase(c2)

	c1_selected := false
	c2_selected := false
	for {
		selected_case := channel.TwoCaseSelect(&case_1, &case_2, false)
		// Make sure we eventually hit the second case
		if selected_case == 0 {
			c1_selected = true
		} else if selected_case == 1 {
			c2_selected = true
		}
		if c1_selected && c2_selected {
			break
		}

	}

}

// Same as above but swap the case order to make sure it works symmetrically i.e. the
// implementation doesn't have the same problem in the opposite order.
func TestSelectLivenessOrder2(t *testing.T) {
	c1 := channel.NewChannelRef[uint64](uint64(0))
	c2 := channel.NewChannelRef[uint64](uint64(1))
	case_1 := channel.NewRecvCase(c1)
	case_2 := channel.NewRecvCase(c2)

	c1.Close()
	c2.Send(0)
	c1_selected := false
	c2_selected := false
	for {
		selected_case := channel.TwoCaseSelect(&case_2, &case_1, false)
		// Make sure we eventually hit the second case
		if selected_case == 0 {
			c1_selected = true
		} else if selected_case == 1 {
			c2_selected = true
		}
		if c1_selected && c2_selected {
			break
		}

	}

}

// Make sure if we keep selecting and 1 case is immediately selectable we still can choose a case
// that eventually becomes selectable.
func TestSelectLivenessNotImmediatelySelectable(t *testing.T) {
	c1 := channel.NewChannelRef[uint64](uint64(0))
	c2 := channel.NewChannelRef[uint64](uint64(0))
	case_1 := channel.NewRecvCase(c1)
	case_2 := channel.NewRecvCase(c2)

	c1.Close()
	c1_selected := false
	c2_selected := false
	go func() {
		for {
			selected_case := channel.TwoCaseSelect(&case_2, &case_1, false)
			// Make sure we eventually hit the second case
			if selected_case == 0 {
				c1_selected = true
			} else if selected_case == 1 {
				c2_selected = true
			}
			if c1_selected && c2_selected {
				break
			}
		}
	}()
	time.Sleep(time.Millisecond * 10)
	c2.Send(0)

}

// Make sure a selectable buffered channel case isn't selected every time if it
// appears first
func TestSelectFairnessWithBufferedChannel(t *testing.T) {
	// Create one buffered and one unbuffered channel
	c1 := channel.NewChannelRef[int](1) // Buffered (capacity 1)
	c2 := channel.NewChannelRef[int](0) // Unbuffered

	// Create select cases - buffered channel first
	case1 := channel.NewRecvCase(c1)
	case2 := channel.NewRecvCase(c2)

	// Put data in the buffered channel to make it immediately ready
	c1.Send(42)

	// Channel to signal test completion
	done := channel.NewChannelRef[bool](0)

	buffered_selected := false
	unbuffered_selected := false

	// Start a goroutine that selects until both channels have been chosen
	go func() {
		for {
			selected_case := channel.TwoCaseSelect(&case1, &case2, true)

			if selected_case == 0 {
				buffered_selected = true
				// Refill the buffered channel
				c1.Send(42)
			} else if selected_case == 1 {
				unbuffered_selected = true
			}

			if buffered_selected && unbuffered_selected {
				done.Send(true)
				return
			}
		}
	}()

	// Send to the unbuffered channel
	c2.Send(99)

	// Wait for the test to complete
	result := done.ReceiveDiscardOk()

	// The done channel will only receive a value if both channels were selected
	if !result {
		t.Fatal("Test did not complete successfully")
	}
}
