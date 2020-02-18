package semantics

import "github.com/tchajed/goose/machine"

// helpers
func stringAppend(s string, x uint64) string {
	return s + machine.UInt64ToString(x)
}

func stringLength(s string) uint64 {
	return uint64(len(s))
}

// tests
func failing_testStringAppend() bool {
	var ok = true
	var s = "123"

	var y = stringAppend(s, 45)
	return ok && (y == "12345")
}

func failing_testStringLength() bool {
	var ok = true
	var s = ""

	ok = ok && (uint64(len(s)) == 0)

	s = stringAppend(s, 1)
	ok = ok && (uint64(len(s)) == 1)

	s = stringAppend(s, 23)

	return ok && (uint64(len(s)) == 3)
}
