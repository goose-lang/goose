package unittest

import (
	"sync"

	"github.com/tchajed/goose/machine"
)

// Skip is a placeholder for some impure code
func Skip() {}

func simpleSpawn() {
	l := new(sync.RWMutex)
	v := new(uint64)
	machine.Spawn(func() {
		l.RLock()
		x := *v
		if x > 0 {
			Skip()
		}
		l.RUnlock()
	})
	l.Lock()
	*v = 1
	l.Unlock()
}

func threadCode(tid uint64) {}

func loopSpawn() {
	for i := uint64(0); i < 10; i++ {
		i := i
		machine.Spawn(func() {
			threadCode(i)
		})
	}
	for dummy := true; ; {
		// do some work to avoid a self-assignment
		dummy = !dummy
		continue
	}
}
