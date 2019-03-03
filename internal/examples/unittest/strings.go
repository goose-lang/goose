package unittest

import "github.com/tchajed/goose/machine"

func StringAppend(s string, x uint64) string {
	return "prefix " + s + " " + machine.UInt64ToString(x)
}
