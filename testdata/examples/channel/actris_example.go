package channel_examples

// prog3 from Actris 2.0 intro: https://arxiv.org/pdf/2010.15030
func DSPExample() int {
	c := make(chan any)
	signal := make(chan any)

	go func() {
		ptr := (<-c).(*int)
		*ptr = *ptr + 2
		signal <- struct{}{}
	}()

	val := 40
	ptr := &val // create reference to 40
	c <- ptr
	<-signal
	return *ptr // dereference to get 42
}
