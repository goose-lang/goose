package example

func Skip() {}

func BadIf2(i uint64) {
	if i == 0 {
		if true { // ERROR nested if statement branches differ on whether they return
			return
		} else {
			Skip()
		}
	}
	Skip()
}
