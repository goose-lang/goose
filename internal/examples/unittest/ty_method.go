package unittest

type TyMethodSl []byte

func (o TyMethodSl) func1() {}

func (o *TyMethodSl) func2() {}

type TyMethodInt uint64

func (o TyMethodInt) func1() {}

func (o *TyMethodInt) func2() {}

// Test both ptr and direct receiver methods since there's a tricky corner case there.
func TyMethodDriver() {
	oSl := TyMethodSl([]byte{})
	oSlPtr := &oSl
	oSl.func1()
	oSlPtr.func2()

	oInt := TyMethodInt(1)
	oIntPtr := &oInt
	oInt.func1()
	oIntPtr.func2()
}
