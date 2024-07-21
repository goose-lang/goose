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

func testAssignConcreteToInterface(x *Fooer) {
	c := &concreteFooer{}
	*x = c
}

func testPassConcreteToInterfaceArg() {
	c := &concreteFooer{}
	fooConsumer(c)

	var f Fooer = c
	fooConsumer(f)
	c.Foo()
	f.Foo()
}

func testPassConcreteToInterfaceArgSpecial() ([]Fooer, map[uint64]Fooer, FooerUser) {
	c1 := &concreteFooer{}
	c2 := &concreteFooer{}

	l := []Fooer{c1, c2}

	m := make(map[uint64]Fooer)
	m[10] = c1

	f := FooerUser{c1}

	return l, m, f
}

func returnConcrete() (*concreteFooer, uint64) {
	return &concreteFooer{}, 10
}

// converts an object into an interface in a multiple return destructuring statement.
func testMultiReturn(x *Fooer) uint64 {
	var y uint64
	*x, y = returnConcrete()
	return y
}

func testReturnStatment() Fooer {
	var y *concreteFooer = &concreteFooer{}
	return y
}
