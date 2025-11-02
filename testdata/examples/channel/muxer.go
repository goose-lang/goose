package chan_spec_raw_examples

type stream struct {
	req chan string
	res chan string
	f   func(string) string
}

func mkStream(f func(string) string) stream {
	return stream{make(chan string), make(chan string), f}
}

// 1. Async - simplest building block
func Async(f func() string) chan string {
	ch := make(chan string, 1)
	go func() {
		ch <- f()
	}()
	return ch
}

// 2. MapServer - handles a single stream
func MapServer(s stream) {
	for in := range s.req {
		s.res <- s.f(in)
	}
}

// 3. Muxer - SPSC for streams
func Muxer(c chan stream) {
	for s := range c {
		go MapServer(s)
	}
}

// 4. CancellableMuxer - muxer with cancellation
func CancellableMuxer(c chan stream, done chan struct{}) {
	for {
		select {
		case s, ok := <-c:
			if !ok {
				return
			}
			go MapServer(s)
		case <-done:
			return
		}
	}
}
