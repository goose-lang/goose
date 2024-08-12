package unittest

// import "github.com/goose-lang/primitive"

func clearMap(m map[uint64]uint64) {
	// primitive.MapClear(m)
}

func IterateMapKeys(m map[uint64]uint64, sum *uint64) {
	for k := range m {
		oldSum := *sum
		*sum = oldSum + k
	}
}

func MapSize(m map[uint64]bool) uint64 {
	return uint64(len(m))
}

type IntWrapper uint64

type MapWrapper map[uint64]bool

func MapTypeAliases(m1 map[IntWrapper]bool, m2 MapWrapper) {
	m1[4] = m2[uint64(0)]
}

func StringMap(m map[string]uint64) uint64 {
	return m["foo"]
}

type mapElem struct {
	a uint64
	b uint64
}

func mapUpdateField() {
	x := make(map[uint64]*mapElem)
	x[0].a = 10
}
