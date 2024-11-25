package unittest

func foo() uint64 {
	return 10
}

var globalX uint64 = foo()
var globalY string

func other() {
	globalY = "ok"
}

func bar() {
	other()
	if x != 10 || globalY != "ok" {
		panic("bad")
	}
}
