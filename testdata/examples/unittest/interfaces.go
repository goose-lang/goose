package unittest

type Fooer interface {
	Foo()
}

type concreteFooer struct {
	a uint64
}

func (f *concreteFooer) Foo() {
}

func fooConsumer(f Fooer) {
	f.Foo()
}

func m() {
	c := &concreteFooer{}
	fooConsumer(c)

	var f Fooer = c
	fooConsumer(f)
	c.Foo()
	f.Foo()
}
