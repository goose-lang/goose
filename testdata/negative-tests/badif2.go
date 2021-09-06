package example

func Skip() {}

func BadIf2(i uint64) {
	if i == 0 {
		if true { // ERROR return in unsupported position
			return
		} else {
			Skip()
		}
	}
	Skip()
}
