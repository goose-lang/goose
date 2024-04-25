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

// From Go spec: "note that the zero value for a slice or map type is not the
// same as an initialized but empty value of the same type".
func compositeLitLenZero() []byte {
	return []byte{}
}
