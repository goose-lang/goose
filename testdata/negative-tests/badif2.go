package example

func Skip() {}

func BadIf2(i uint64) {
	if i == 0 {
		if true {
			return // ERROR return in unsupported position
		} else {
			Skip()
		}
	}
	Skip()
}
