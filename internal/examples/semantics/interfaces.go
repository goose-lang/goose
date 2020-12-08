package semantics

type geometryInterface interface {
	Square() uint64
	Volume() uint64
}

func measureSquare(t geometryInterface) uint64 {
	return t.Square()
}

func measureVolume(t geometryInterface, e uint64, s string) uint64 {
	return t.Volume()
}

type SquareStruct struct {
	Side uint64
}

func (t SquareStruct) Square() uint64 {
	return t.Side * t.Side
}

func (t SquareStruct) Volume() uint64 {
	return t.Side * t.Side * t.Side
}

func testBasicInterface() bool {
	s := SquareStruct{
		Side: 2,
	}
	return measureSquare(s) == 4
}

func testAssignInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square := measureSquare(s)
	return square == 9
}

func testParamsInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	volume := measureVolume(s, 5, "string")
	return volume == 32
}

// ----------------------------

type bookInterface interface {
	GetAuthor() string
}

type authorInterface interface {
	GetBirthdate() uint64
}

type BookStruct struct {
	Author string
}

type AuthorStruct struct {
	Birthdate uint64
}

func (b BookStruct) GetAuthor() string {
	return b.Author
}

func (a AuthorStruct) GetBirthdate() uint64 {
	return a.Birthdate
}

func WhichAuthor(b bookInterface) string {
	return b.GetAuthor()
}

func WhichBirthdate(a authorInterface) uint64 {
	return a.GetBirthdate()
}

// Make sure mutliple interfaces are translated
func multipleInterfacesTest() bool {
	b := BookStruct{
		Author: "Steve",
	}
	a := AuthorStruct{
		Birthdate: 11011998,
	}
	return WhichAuthor(b) == "Steve" && WhichBirthdate(a) == 11011998
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

// type shapeInterface interface {
// 	describe() string
// }

// type polygonInterface interface {
// 	sides() uint64
// }

// type shapeStruct struct {
// 	Shape string
// }

// func (s shapeStruct) describe() string {
// 	return s.Shape
// }

// type polygonStruct struct {
// 	Shape string
// 	Sides uint64
// }

// func (p polygonStruct) describe() string {
// 	return p.Shape
// }

// func (p polygonStruct) sides() uint64 {
// 	return p.Sides
// }

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
