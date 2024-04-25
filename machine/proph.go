package machine

// Prophecy variables.
//
// We represent the name of a prophecy variable via an opaque type. In Go, it
// does not actually carry any data, but in GooseLang we store the ProphId.
// However, making a type opaque in Go seems to be tricky. Let's hope adding a
// private field helps.
//
//lint:ignore U1000 p is unused, see above comment.
type prophId struct{ p struct{} }
type ProphId = *prophId

func NewProph() ProphId {
	return &prophId{}
}

func (p ProphId) ResolveBool(b bool)  {}
func (p ProphId) ResolveU64(i uint64) {}
