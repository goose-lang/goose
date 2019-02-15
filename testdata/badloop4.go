package example

func NoInit() {
	for { // ERROR loop without a loop variable
		break
	}
}
