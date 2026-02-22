package leakbuffer

// LeakyBuffer is a fixed-size leaky freelist for []byte, plus an owned channel serverChan for
// sending populated bytes.
//
// Acquire is nonblocking and will allocate a byte[] if one is not available.
// Release is nonblocking and will free the byte[] if there isn't room in the buffer.
//
// Sending to the server channel is intentionally NOT abstracted away, so callers can
// select/multiplex on it directly via ServerChan().
// See https://go.dev/doc/effective_go#leaky_buffer
type LeakyBuffer struct {
	// For sending populated data from client to server
	serverChan chan []byte
	// For returning processed buffers to the client
	free chan []byte
	// The capacity of each []byte
	bufCap int
}

// NewLeakyBuffer creates a LeakyBuffer with:
// - maxFree: max number of buffers kept for reuse
// - bufCap: capacity of each buffer
// - serverChan: channel used to hand off full buffers to the server.
func NewLeakyBuffer(maxFree int, maxInflight int, bufCap int) *LeakyBuffer {
	return &LeakyBuffer{
		serverChan: make(chan []byte, maxInflight),
		free:       make(chan []byte, maxFree),
		bufCap:     bufCap,
	}
}

// ServerChan exposes the send-only server channel so callers can select on sends.
func (lb *LeakyBuffer) ServerChan() chan<- []byte {
	return lb.serverChan
}

// Acquire returns a buffer with len=0 and cap=lb.bufCap.
// It never blocks: reuse if available, else allocate.
func (lb *LeakyBuffer) Acquire() []byte {
	select {
	case b := <-lb.free:
		return b[:0]
	default:
		return make([]byte, 0, lb.bufCap)
	}
}

// Release attempts to return the buffer to the freelist.
// It never blocks: if freelist is full, the buffer is dropped ("leaky").
func (lb *LeakyBuffer) TryRelease(b []byte) {
	select {
	case lb.free <- b:
	default:
	}
}
