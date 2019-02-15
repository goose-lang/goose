package example

func loopCond() {
	for i := uint64(0); i < 3; { // ERROR condition
	}
}
