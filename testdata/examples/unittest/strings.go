package unittest

import "github.com/goose-lang/primitive"

func stringAppend(s string, x uint64) string {
	return "prefix " + s + " " + primitive.UInt64ToString(x)
}

func stringLength(s string) uint64 {
	return uint64(len(s))
}
