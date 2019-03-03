package unittest

// DoSomething is an impure function
func DoSomething(s string) {}

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
