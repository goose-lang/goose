package example

func Skip() bool { return false }

func BadLoop(i uint64) {
	// This used to translate incorrectly, into a loop that always `Continue`s.
	for {
		if !Skip() { // ERROR nested if statement branches differ on whether they return
			break
		}
	}
}
