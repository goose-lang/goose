package semantics

import (
	"github.com/tchajed/goose/machine"
	"sync"
)

func testLinearize() bool {
	m := new(sync.Mutex)
	m.Lock()
	machine.Linearize()
	m.Unlock()
	return true
}
