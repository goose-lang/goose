package example

func Skip() {}

func BadIf2(i uint64) {
	if i == 0 {
		if true {
			return // ERROR nested if statement branches differ on whether they return
		} else {
			Skip()
		}
	}
	Skip()
}
