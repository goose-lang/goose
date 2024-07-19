package unittest

import "github.com/goose-lang/goose/machine"

func Oracle() {
	p := machine.NewProph()
	p.ResolveBool(false)
	p.ResolveU64(0)
}

type typing struct {
	proph machine.ProphId
}
