package unittest

type allTheLiterals struct {
	int uint64
	s   string
	b   bool
}

func normalLiterals() allTheLiterals {
	return allTheLiterals{
		int: 0,
		s:   "foo",
		b:   true,
	}
}

func specialLiterals() allTheLiterals {
	return allTheLiterals{
		int: 4096,
		s:   "",
		b:   false,
	}
}

func oddLiterals() allTheLiterals {
	return allTheLiterals{
		int: 5,
		s:   `backquote string`,
		b:   false,
	}
}

func unKeyedLiteral() allTheLiterals {
	return allTheLiterals{0, "a", false}
}
