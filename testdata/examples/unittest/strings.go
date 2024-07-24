package unittest

import "github.com/goose-lang/goose/machine"

func stringAppend(s string, x uint64) string {
	return "prefix " + s + " " + machine.UInt64ToString(x)
}

func stringLength(s string) uint64 {
	return uint64(len(s))
}
