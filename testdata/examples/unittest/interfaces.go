package unittest

type Fooer interface {
	Foo()
}

type concreteFooer struct {
	a uint64
}

type FooerUser struct {
	f Fooer
}

func (f *concreteFooer) Foo() {
}

func fooConsumer(f Fooer) {
	f.Foo()
}

func assignConcreteToInterface(x *Fooer) {
	c := &concreteFooer{}
	*x = c
}

func passConcreteToInterfaceArg() {
	c := &concreteFooer{}
	fooConsumer(c)

	var f Fooer = c
	fooConsumer(f)
	c.Foo()
	f.Foo()
}

func passConcreteToInterfaceArgSpecial() ([]Fooer, map[uint64]Fooer, FooerUser) {
	c1 := &concreteFooer{}
	c2 := &concreteFooer{}

	l := []Fooer{c1, c2}

	m := make(map[uint64]Fooer)
	m[10] = c1

	f := FooerUser{c1}

	return l, m, f
}
