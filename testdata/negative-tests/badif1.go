package example

func Skip() {}

func BadIf(i uint64) {
	if i == 0 {
		return
	} else { // ERROR early return in if with an else branch
		Skip()
	}
	Skip()
}
