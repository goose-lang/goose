package semantics

// ----------------------------
// SETUP
// ----------------------------

type geometryInterface interface {
	Square() uint64
	Volume() uint64
}

func measureSquare(t geometryInterface) uint64 {
	return t.Square()
}

func measureVolumePlusN(t geometryInterface, n uint64) uint64 {
	return t.Volume() + n
}

func measureVolume(t geometryInterface) uint64 {
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

// ----------------------------
// TESTS
// ----------------------------

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

func failing_testParamsInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	volume := measureVolumePlusN(s, 1)
	return volume == 28
}

func testMultipleInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square1 := measureSquare(s)
	square2 := measureSquare(s)
	return square1 == square2
}

func testBinaryExprInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square1 := measureSquare(s)
	square2 := measureVolume(s)
	return square1 == measureSquare(s) && square2 == measureVolume(s)
}

func testIfStmtInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	if measureSquare(s) == 9 {
		return true
	}
	return false
}
