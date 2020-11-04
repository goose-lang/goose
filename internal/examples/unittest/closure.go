package unittest

func adder() func(uint64) uint64 {
	var sum = uint64(0)
	return func(x uint64) uint64 {
		sum += x
		return sum
	}
}

func main() {
	pos := adder()
	doub := adder()
	for i := uint64(0); i < 10; i++ {
		pos(i)
		doub(2 * i)
	}
}
