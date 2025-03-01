package unittest

func chan_stuff(c chan uint64, d chan uint64) <-chan uint64 {
	var to_send uint64 = 0
	c <- to_send
	return d
}

func main() {
	c := make(chan uint64)
	d := make(chan uint64)
	c <- 1
	close(d)
	var u uint64 = <-c
	var v uint64
	var ok bool
	v, ok = <-d
	ok = !ok
	u++
	v++
}
