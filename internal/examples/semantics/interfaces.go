package semantics

type squareInterface interface {
	Square() uint64
}

func measureSquare(t squareInterface) uint64 {
	return t.Square()
}

type NumStruct struct {
	Number uint64
}

func (t NumStruct) Square() uint64 {
	return t.Number * t.Number
}

func testBasicInterface() bool {
	s := NumStruct{
		Number: 2,
	}

	return measureSquare(s) == 4
}

func testAssignInterface() bool {
	s := NumStruct{
		Number: 3,
	}

	square := measureSquare(s)
	return square == 9
}

// Failing
// func testEmptyInterface() bool {
// 	var i interface{}
// 	var j interface{}

// 	return i == j
// }

// Failing
// func testStringInterface() bool {
// 	var i interface{} = "string"
// 	var j interface{} = "string"

// 	return i == j
// }

// func testTypeAssertionInterface() bool {
// 	var i interface{} = NumStruct{3}

// 	return i.(NumStruct) == NumStruct{3}
// }

// func testMultipleInterface() bool {
// 	s := NumStruct{
// 		Number: 3,
// 	}

// 	square1 := measureSquare(s)
// 	square2 := measureSquare(s)

// 	return square1 == square2
// }

type shapeInterface interface {
	describe() string
}

type polygonInterface interface {
	sides() uint64
}

type shapeStruct struct {
	Shape string
}

func (s shapeStruct) describe() string {
	return s.Shape
}

type polygonStruct struct {
	Shape string
	Sides uint64
}

func (p polygonStruct) describe() string {
	return p.Shape
}

func (p polygonStruct) sides() uint64 {
	return p.Sides
}

// func doublePointerInterfaceTest() bool {
// 	s := shapeStruct{"circle"}
// 	shapes := []shapeInterface{s, &s}

// 	s.Shape = "square"

// 	return shapes[0].describe() != shapes[1].describe()
// }

// func multipleFieldsInterfaceTest() bool {
// 	s := polygonStruct{"triangle", 3}

// 	return s.Shape == "triangle" && s.Sides == 3
// }

// type dogInterface interface {
// 	Name() string
// 	Speed() uint64
// }

// type catInterface interface {
// 	Name() string
// 	Weight() uint64
// }

// type Puppy string

// func (p Puppy) Name() string {
// 	return "Max"
// }

// func (p Puppy) Speed() uint64 {
// 	return 1
// }

// type Kitten string

// func (k Kitten) Name() string {
// 	return "Max"
// }

// func (k Kitten) Weight() uint64 {
// 	return 10
// }

// func sharedFunctionsInterfaceTest() bool {
// 	var kit catInterface = Kitten("Kitten")
// 	var pup dogInterface = Puppy("Puppy")

// 	return pup.Name() == kit.Name()
// }

type bookInterface interface {
	GetAuthor() string
}

type NovelStruct struct {
	Author string
}

func (n NovelStruct) GetAuthor() string {
	return n.Author
}

func WhichAuthor(b bookInterface) string {
	return b.GetAuthor()
}

func interfaceMethodNoParamsTest() bool {
	n := NovelStruct{
		Author: "Steve",
	}

	return WhichAuthor(n) == "Steve"
}

// type printInterface interface {
// 	Assign(string)
// 	GetTitle() string
// }

// type PaperStruct struct {
// 	Title string
// }

// func (p *PaperStruct) Assign(t string) {
// 	p.Title = t
// }

// func (p *PaperStruct) GetTitle() string {
// 	return p.Title
// }

// func acceptAddressInterfaceTest() bool {
// 	var p1 PaperStruct
// 	var p2 PaperStruct
// 	p1.Assign("Sample Title")
// 	p2.Assign("Sample Title")

// 	var print1 printInterface
// 	var print2 printInterface

// 	print1 = &p1
// 	print2 = &p2

// 	return print1.GetTitle() == print2.GetTitle()
// }

// type Flower interface {
// 	Petals() uint64
// }

// type Flora interface {
// 	Flower
// 	Genus() string
// }

// type Lily struct{}

// func (l Lily) Petals() uint64 { return 3 }
// func (l Lily) Genus() string  { return "Lillium" }

// type Rose struct{}

// func (r Rose) Petals() uint64 { return 12 }
// func (r Rose) Genus() string  { return "Rosa" }

// type Daisy struct{}

// func (d Daisy) Petals() uint64 { return 5 }
// func (d Daisy) Genus() string  { return "Bellis" }

// func polymorphismInterfaceTest() bool {
// 	l := new(Lily)
// 	r := new(Rose)
// 	d := new(Daisy)
// 	f := [...]Flower{l, r, d}

// 	return f[0].Petals() == 3
// }

// func embeddingInterfaceTest() bool {
// 	l := new(Lily)
// 	r := new(Rose)
// 	d := new(Daisy)
// 	f := [...]Flora{l, r, d}

// 	return f[0].Petals() == 3
// }

// func downcastInterfaceTest() bool {
// 	l := Lily{}
// 	var f Flora = l
// 	return f.Petals() == f.(Flower).Petals()
// }

// slices, maps not supported
