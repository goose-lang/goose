package unittest

import "sync"

func Skip() {}

func SimpleSpawn() {
	l := new(sync.RWMutex)
	v := new(uint64)
	go func() {
		l.RLock()
		x := *v
		if x > 0 {
			Skip()
		}
		l.RUnlock()
	}()
	l.Lock()
	*v = 1
	l.Unlock()
}
