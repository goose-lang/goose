package unittest

const GlobalConstant string = "foo"

const UntypedStringConstant = "bar" // an untyped string

const TypedInt uint64 = 32

const ConstWithArith uint64 = 4 + 3*TypedInt

const TypedInt32 uint32 = 3

const DivisionInConst uint64 = (4096 - 8) / 8

const ModInConst uint64 = 513 + 12%8 // 517

const ModInConstParens uint64 = (513 + 12) % 8 // 5
