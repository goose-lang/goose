package machine

// Wrap goose-lang/primitive for backwards compatibility

import "github.com/goose-lang/primitive"

type ProphId = primitive.ProphId

func NewProph() ProphId {
	return primitive.NewProph()
}
