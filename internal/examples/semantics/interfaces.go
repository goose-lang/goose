package semantics

import "fmt"

// Interface with method set
type testInterface interface {
	Square() uint64
}

// Empty interface
type emptyInterface interface{}

func returnSquare(t testInterface) uint64 {
	return t.Square()
}

type TestStruct struct {
	Number uint64
}

func (t TestStruct) Square() uint64 {
	return t.Number * t.Number
}

func test() {
	s := TestStruct{
		Number: 2,
	}

	fmt.Println("%d", uint64(returnSquare(s)))
}
