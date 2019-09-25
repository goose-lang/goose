package unittest

// DoSomething is an impure function
func DoSomething(s string) {}

func standardForLoop(s []uint64) uint64 {
	// this is the boilerplate needed to do a normal for loop
	sumPtr := new(uint64)
	for i := uint64(0); ; {
		if i < uint64(len(s)) {
			// the body of the loop
			sum := *sumPtr
			x := s[i]
			*sumPtr = sum + x

			i = i + 1
			continue
		}
		break
	}
	sum := *sumPtr
	return sum
}

func conditionalInLoop() {
	for i := uint64(0); ; {
		if i < 3 {
			DoSomething("i is small")
		}
		if i > 5 {
			break
		}
		i = i + 1
		continue
	}
}
