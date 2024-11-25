package unittest

func foo() uint64 {
	return 10
}

var GlobalX uint64 = foo()
var globalY string

func other() {
	globalY = "ok"
}

func bar() {
	other()
	if GlobalX != 10 || globalY != "ok" {
		panic("bad")
	}
}
