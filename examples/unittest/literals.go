package unittest

type allTheLiterals struct {
	int uint64
	s   string
	// that's it!
}

func normalLiterals() allTheLiterals {
	return allTheLiterals{
		int: 0,
		s:   "foo",
	}
}

func specialLiterals() allTheLiterals {
	return allTheLiterals{
		int: 4096,
		s:   "",
	}
}

func oddLiterals() allTheLiterals {
	return allTheLiterals{
		int: 5,
		s:   `backquote string`,
	}
}
