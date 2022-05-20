package example

func PointerToFunction(p *func()) {
	f := *p // ERROR function type
	f()
}
