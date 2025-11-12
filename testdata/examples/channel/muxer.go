package chan_spec_raw_examples

type stream struct {
	req chan string
	res chan string
	f   func(string) string
}

func mkStream(f func(string) string) stream {
	return stream{make(chan string), make(chan string), f}
}

func Async(f func() string) chan string {
	ch := make(chan string, 1)
	go func() {
		ch <- f()
	}()
	return ch
}

func MapServer(s stream) {
	for {
		in := <-s.req
		s.res <- s.f(in)
	}
}

func Client() string {

	comma := mkStream(func(s string) string { return s + "," })
	exclaim := mkStream(func(s string) string { return s + "!" })

	go MapServer(comma)
	go MapServer(exclaim)

	// Use them
	comma.req <- "Hello"
	exclaim.req <- "World"

	return <-comma.res + " " + <-exclaim.res
}

func Muxer(c chan stream) {
	for s := range c {
		go MapServer(s)
	}
}

func CancellableMapServer(s stream, done chan struct{}) {
	for {
		select {
		case in, ok := <-s.req:
			if !ok {
				return
			}
			s.res <- s.f(in)
		case <-done:
			return
		}
	}
}

// 4. CancellableMuxer - muxer with cancellation
func CancellableMuxer(c chan stream, done chan struct{}, errMsg *string) string {
	for {
		select {
		case s, ok := <-c:
			if !ok {
				return "serviced all requests"
			}
			go CancellableMapServer(s, done)
		case <-done:
			return *errMsg
		}
	}
}

func makeGreeting() string {
	// Start muxer
	mux := make(chan stream, 2)
	go Muxer(mux)

	// Two simple streams
	comma := mkStream(func(s string) string { return s + "," })
	exclaim := mkStream(func(s string) string { return s + "!" })

	// Submit to muxer
	mux <- comma
	mux <- exclaim

	// Use them
	comma.req <- "Hello"
	exclaim.req <- "World"

	return <-comma.res + " " + <-exclaim.res
}
