package unittest

type embedA struct {
	a uint64
}

type embedB struct {
	embedA
}

type embedC struct {
	*embedB
}

type embedD struct {
	embedC
}

func (a embedA) Foo() uint64 {
	return 0
}

func (a embedB) Foo() uint64 {
	return 10
}

func returnEmbedVal() embedB {
	return embedB{}
}

func returnEmbedValWithPointer() embedD {
	return embedD{}
}

func useEmbeddedField(d embedD) uint64 {
	x := d.embedB.a
	x = d.a
	return x
}

func useEmbeddedValField() uint64 {
	x := returnEmbedVal().a
	x = returnEmbedValWithPointer().a
	return x
}

func useEmbeddedMethod(d embedD) bool {
	return d.Foo() == d.embedB.Foo()
}
