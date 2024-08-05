package unittest

import "github.com/goose-lang/primitive"

func Oracle() {
	p := primitive.NewProph()
	p.ResolveBool(false)
	p.ResolveU64(0)
}

type typing struct {
	proph primitive.ProphId
}
