package semantics

import (
	"sync"

	"github.com/goose-lang/goose/machine"
)

func testLinearize() bool {
	m := new(sync.Mutex)
	m.Lock()
	machine.Linearize()
	m.Unlock()
	return true
}
