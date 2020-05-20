package semantics

import "fmt"

type shape interface {
	area() uint64
	perim() uint64
}

type rect struct {
	width  uint64
	height uint64
}

func (r rect) area() uint64 {
	return r.width * r.height
}

func (r rect) perim() uint64 {
	return 2*r.width + 2*r.height
}

func measure(s shape) {
	fmt.Println(s)
	fmt.Println(s.area())
	fmt.Println(s.perim())
}
