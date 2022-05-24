package example

type IntMap[T any] map[uint64]T // ERROR generic named type
