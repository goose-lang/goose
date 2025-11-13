package chan_spec_raw_examples

type stream struct {
	req chan string
	res chan string
}

type streamold struct {
	req chan string
	res chan string
	f   func(string) string
}

func mkStream(f func(string) string) streamold {
	return streamold{make(chan string), make(chan string), f}
}

func Async(f func() string) chan string {
	ch := make(chan string, 1)
	go func() {
		ch <- f()
	}()
	return ch
}

func Serve(f func(string) string) stream {
	s := stream{
		req: make(chan string),
		res: make(chan string),
	}
	go func() {
		for {
			s.res <- f(<-s.req)
		}
	}()
	return s
}

func appWrld(s string) string {
	return s + ", World!"
}

func Client() string {
	hw := Serve(appWrld)
	hw.req <- "Hello"
	return <-hw.res
}

func MapServer(s streamold) {
	for {
		in := <-s.req
		s.res <- s.f(in)
	}
}

func ClientOld() string {

	comma := mkStream(func(s string) string { return s + "," })
	exclaim := mkStream(func(s string) string { return s + "!" })

	go MapServer(comma)
	go MapServer(exclaim)

	// Use them
	comma.req <- "Hello"
	exclaim.req <- "World"

	return <-comma.res + " " + <-exclaim.res
}

func Muxer(c chan streamold) {
	for s := range c {
		go MapServer(s)
	}
}

func CancellableMapServer(s streamold, done chan struct{}) {
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
func CancellableMuxer(c chan streamold, done chan struct{}, errMsg *string) string {
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
	mux := make(chan streamold, 2)
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
