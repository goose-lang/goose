package semantics

// Interface with method set
type testInterface interface {
	Square() uint64
}

// Empty interface
type emptyInterface interface{}

func measureSquare(t testInterface) uint64 {
	return t.Square()
}

type TestStruct struct {
	Number uint64
}

func (t TestStruct) Square() uint64 {
	return t.Number * t.Number
}

func interfaceTest() bool {
	s := TestStruct{
		Number: 2,
	}

	return measureSquare(s) == 4
}
