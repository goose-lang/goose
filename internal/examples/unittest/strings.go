package unittest

import "github.com/tchajed/goose/machine"

func stringAppend(s string, x uint64) string {
	return "prefix " + s + " " + machine.UInt64ToString(x)
}
