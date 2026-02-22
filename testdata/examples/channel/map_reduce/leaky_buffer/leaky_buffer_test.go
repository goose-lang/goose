package leakbuffer

import (
	"bufio"
	"bytes"
	"strings"
	"testing"
	"time"
)

// helper: must not block longer than d
func mustReturnWithin(t *testing.T, d time.Duration, fn func()) {
	t.Helper()
	done := make(chan struct{})
	go func() {
		defer close(done)
		fn()
	}()
	select {
	case <-done:
		return
	case <-time.After(d):
		t.Fatalf("operation did not return within %s (likely blocked)", d)
	}
}

func TestAcquireAllocatesWhenFreeEmpty(t *testing.T) {
	lb := NewLeakyBuffer(0, 0, 128)

	b := lb.Acquire()
	if b == nil {
		t.Fatalf("Acquire returned nil buffer")
	}
	if len(b) != 0 {
		t.Fatalf("len(b)=%d, want 0", len(b))
	}
	if cap(b) != 128 {
		t.Fatalf("cap(b)=%d, want 128", cap(b))
	}
}

func TestAcquireReuseResetsLen(t *testing.T) {
	lb := NewLeakyBuffer(1, 0, 64)

	// Acquire new, grow len, then release.
	b1 := lb.Acquire()
	b1 = append(b1, 1, 2, 3, 4, 5)
	if len(b1) == 0 {
		t.Fatalf("expected non-empty after append")
	}
	lb.TryRelease(b1)

	// Acquire should reuse and reset len to 0.
	b2 := lb.Acquire()
	if len(b2) != 0 {
		t.Fatalf("len(b2)=%d, want 0 (Acquire should reset len)", len(b2))
	}
	if cap(b2) != 64 {
		t.Fatalf("cap(b2)=%d, want 64", cap(b2))
	}

	// Best-effort reuse check: when maxFree=1 and we released exactly once,
	// it should come back as the same underlying array.
	if cap(b2) != cap(b1) {
		t.Fatalf("cap changed across reuse: cap(b1)=%d cap(b2)=%d", cap(b1), cap(b2))
	}
}

func TestTryReleaseIsNonBlockingWhenFreeFull(t *testing.T) {
	lb := NewLeakyBuffer(1, 0, 16)

	// Fill free list to capacity.
	b1 := lb.Acquire()
	lb.TryRelease(b1)

	// Now free list is full; releasing another should not block.
	b2 := lb.Acquire()
	mustReturnWithin(t, 50*time.Millisecond, func() {
		lb.TryRelease(b2)
	})
}

func TestAcquireIsNonBlockingWhenFreeEmpty(t *testing.T) {
	lb := NewLeakyBuffer(0, 0, 32)

	mustReturnWithin(t, 50*time.Millisecond, func() {
		_ = lb.Acquire()
	})
}

func TestServerChan(t *testing.T) {
	lb := NewLeakyBuffer(0, 1, 8) // inflight buffer size 1 so send can succeed without receiver

	out := lb.ServerChan()

	// Should be able to send without blocking (buffered chan of size 1).
	mustReturnWithin(t, 50*time.Millisecond, func() {
		out <- []byte{1, 2, 3}
	})

	// And the data should arrive on the internal channel.
	select {
	case got := <-lb.serverChan:
		if len(got) != 3 || got[0] != 1 || got[1] != 2 || got[2] != 3 {
			t.Fatalf("unexpected payload: %#v", got)
		}
	case <-time.After(50 * time.Millisecond):
		t.Fatalf("expected to receive from serverChan")
	}
}

func TestServerChanBufferedCapacityRespected(t *testing.T) {
	lb := NewLeakyBuffer(0, 1, 8)
	out := lb.ServerChan()

	// First send should fit.
	mustReturnWithin(t, 50*time.Millisecond, func() {
		out <- []byte{1}
	})

	// Second send should block until someone receives, since maxInflight=1.
	// We test this by asserting it does NOT complete within a short window,
	// then draining and ensuring it completes.
	secondDone := make(chan struct{})
	go func() {
		out <- []byte{2}
		close(secondDone)
	}()

	// Should still be blocked.
	select {
	case <-secondDone:
		t.Fatalf("second send unexpectedly completed; expected it to block with maxInflight=1")
	case <-time.After(30 * time.Millisecond):
		// ok, likely blocked
	}

	// Drain one item so second send can proceed.
	select {
	case <-lb.serverChan:
	case <-time.After(50 * time.Millisecond):
		t.Fatalf("expected to drain first inflight message")
	}

	// Now the second send should finish quickly.
	select {
	case <-secondDone:
	case <-time.After(50 * time.Millisecond):
		t.Fatalf("second send did not complete after draining inflight message")
	}

	// Drain the second message to avoid goroutine leaks / blocked sends in other tests.
	select {
	case got := <-lb.serverChan:
		if len(got) != 1 || got[0] != 2 {
			t.Fatalf("unexpected second payload: %#v", got)
		}
	case <-time.After(50 * time.Millisecond):
		t.Fatalf("expected to receive second inflight message")
	}
}

func TestLeakyBehaviorDropsExcessBuffers(t *testing.T) {
	lb := NewLeakyBuffer(1, 0, 32)

	// Create and release a buffer to fill freelist.
	b1 := lb.Acquire()
	lb.TryRelease(b1)

	// Create another buffer and try to release: should be dropped (nonblocking).
	b2 := lb.Acquire()
	lb.TryRelease(b2)

	// Now only one buffer should be available for reuse from freelist.
	// First acquire will reuse the one in freelist; second acquire will allocate new.
	r1 := lb.Acquire()
	r2 := lb.Acquire()

	// r1 likely reused; r2 must be a fresh allocation (since freelist held only 1).
	// We can't *guarantee* pointer identity, but we can check that after taking r1,
	// freelist is empty, so next Acquire must allocate with correct cap/len.
	if len(r2) != 0 || cap(r2) != 32 {
		t.Fatalf("unexpected r2 shape: len=%d cap=%d", len(r2), cap(r2))
	}

	_ = r1 // silence unused if someone edits the checks above
}

func TestLeakyBufferPipelineUppercase(t *testing.T) {
	input := "hello world\nthis is a test\nleaky buffers are neat\n"
	expected := "HELLO WORLD\nTHIS IS A TEST\nLEAKY BUFFERS ARE NEAT\n"

	lb := NewLeakyBuffer(
		/* maxFree */ 2,
		/* maxInflight */ 2,
		/* bufCap */ 16,
	)

	// Output sink (stand-in for a file).
	var output bytes.Buffer

	// Server goroutine.
	done := make(chan struct{})
	go func() {
		defer close(done)
		for b := range lb.serverChan {
			// Process: uppercase and write.
			upper := bytes.ToUpper(b)
			if _, err := output.Write(upper); err != nil {
				panic(err)
			}
			lb.TryRelease(b)
		}
	}()

	// Client logic: read input line by line, write into buffers, send.
	scanner := bufio.NewScanner(strings.NewReader(input))
	for scanner.Scan() {
		line := scanner.Text() + "\n"

		b := lb.Acquire()
		b = append(b, line...)

		// Explicit send — caller controls this.
		lb.ServerChan() <- b
	}
	if err := scanner.Err(); err != nil {
		t.Fatalf("scanner error: %v", err)
	}

	// Close the server channel to terminate server loop.
	close(lb.serverChan)

	// Wait for server to finish.
	select {
	case <-done:
	case <-time.After(1 * time.Second):
		t.Fatalf("server did not terminate")
	}

	if got := output.String(); got != expected {
		t.Fatalf("unexpected output:\n got: %q\nwant: %q", got, expected)
	}
}

func upperASCIIInPlace(b []byte) {
	for i := 0; i < len(b); i++ {
		c := b[i]
		if c >= 'a' && c <= 'z' {
			b[i] = c - ('a' - 'A')
		}
	}
}

// Safe payload generator: [][]byte, each ends with '\n'.
// (Precompute outside timed region.)
func makePayloadsSafe(numLines, lineLen int) [][]byte {
	pattern := []byte("abcdEFGHijklMNOPqrstUVWXyz12")
	pl := len(pattern)
	if pl == 0 {
		panic("pattern must be non-empty")
	}
	reps := (lineLen / pl) + 1
	base := bytes.Repeat(pattern, reps)[:lineLen]

	payloads := make([][]byte, 0, numLines)
	for i := 0; i < numLines; i++ {
		p := make([]byte, 0, lineLen+1)
		p = append(p, base...)
		p = append(p, '\n')
		if i%3 == 0 && len(p) > 0 {
			p[0] = 'x'
		}
		payloads = append(payloads, p)
	}
	return payloads
}

func expectedUpper(payloads [][]byte) []byte {
	// Deterministic expected output: uppercase each payload and concatenate.
	var out bytes.Buffer
	// Approx size: sum of payload lengths
	total := 0
	for _, p := range payloads {
		total += len(p)
	}
	out.Grow(total)

	tmp := make([]byte, 0, 1024)
	for _, p := range payloads {
		// Make a copy so we can uppercase in-place without mutating payloads.
		if cap(tmp) < len(p) {
			tmp = make([]byte, len(p))
		} else {
			tmp = tmp[:len(p)]
		}
		copy(tmp, p)
		upperASCIIInPlace(tmp)
		_, _ = out.Write(tmp)
	}
	return out.Bytes()
}

func BenchmarkPipeline_LeakyBufferReuseBytes_BufferSink_Validate(b *testing.B) {
	b.ReportAllocs()

	const (
		numLines    = 10000000
		lineLen     = 800
		bufCap      = 1012 // must be >= lineLen+1
		maxFree     = 512
		maxInflight = 64
	)

	b.StopTimer()
	payloads := makePayloadsSafe(numLines, lineLen)
	want := expectedUpper(payloads)
	b.StartTimer()

	for it := 0; it < b.N; it++ {
		lb := NewLeakyBuffer(maxFree, maxInflight, bufCap)
		out := lb.ServerChan()

		var sink bytes.Buffer
		sink.Grow(len(want))

		done := make(chan struct{})
		go func() {
			defer close(done)
			for buf := range lb.serverChan {
				upperASCIIInPlace(buf)
				_, _ = sink.Write(buf)
				lb.TryRelease(buf)
			}
		}()

		for _, p := range payloads {
			buf := lb.Acquire()
			// Copy payload into buf without forcing growth.
			buf = buf[:len(p)]
			copy(buf, p)
			out <- buf
		}

		close(lb.serverChan)
		<-done

		if got := sink.Bytes(); !bytes.Equal(got, want) {
			b.Fatalf("output mismatch (leaky reuse): got %d bytes, want %d bytes", len(got), len(want))
		}
	}
}

func BenchmarkPipeline_AllocateBytesEveryTime_BufferSink_Validate(b *testing.B) {
	b.ReportAllocs()

	const (
		numLines    = 10000000
		lineLen     = 800
		maxInflight = 64
	)

	b.StopTimer()
	payloads := makePayloadsSafe(numLines, lineLen)
	want := expectedUpper(payloads)
	b.StartTimer()

	for it := 0; it < b.N; it++ {
		ch := make(chan []byte, maxInflight)

		var sink bytes.Buffer
		sink.Grow(len(want))

		done := make(chan struct{})
		go func() {
			defer close(done)
			for buf := range ch {
				upperASCIIInPlace(buf)
				_, _ = sink.Write(buf)
			}
		}()

		for _, p := range payloads {
			buf := make([]byte, len(p))
			copy(buf, p)
			ch <- buf
		}

		close(ch)
		<-done

		if got := sink.Bytes(); !bytes.Equal(got, want) {
			b.Fatalf("output mismatch (allocate bytes): got %d bytes, want %d bytes", len(got), len(want))
		}
	}
}

func BenchmarkPipeline_BytesToStringChannel_BufferSink_Validate(b *testing.B) {
	b.ReportAllocs()

	const (
		numLines    = 10000000
		lineLen     = 800
		maxInflight = 64
	)

	b.StopTimer()
	payloads := makePayloadsSafe(numLines, lineLen)
	want := expectedUpper(payloads)
	b.StartTimer()

	for it := 0; it < b.N; it++ {
		ch := make(chan string, maxInflight)

		var sink bytes.Buffer
		sink.Grow(len(want))

		done := make(chan struct{})
		go func() {
			defer close(done)
			for s := range ch {
				// This allocates a new string.
				u := strings.ToUpper(s)
				// WriteString avoids []byte(u) allocation; still writes bytes into sink.
				_, _ = sink.WriteString(u)
			}
		}()

		for _, p := range payloads {
			// Convert bytes -> string (copies).
			ch <- string(p)
		}

		close(ch)
		<-done

		if got := sink.Bytes(); !bytes.Equal(got, want) {
			b.Fatalf("output mismatch (bytes->string): got %d bytes, want %d bytes", len(got), len(want))
		}
	}
}
