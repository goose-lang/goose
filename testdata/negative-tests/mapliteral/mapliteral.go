package example

func mapliteral() map[uint64]uint64 {
	return map[uint64]uint64{1: 2} // ERROR composite literal of type map
}
