package semantics

import (
	"sync"

	"github.com/tchajed/goose/machine"
)

func testLinearize() bool {
	m := new(sync.Mutex)
	m.Lock()
	machine.Linearize()
	m.Unlock()
	return true
}
