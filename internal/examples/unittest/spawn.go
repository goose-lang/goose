package unittest

import "sync"

// Skip is a placeholder for some impure code
func Skip() {}

func simpleSpawn() {
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

func threadCode(tid uint64) {}

func loopSpawn() {
	for i := uint64(0); ; {
		if i > 10 {
			break
		}
		go func(i uint64) {
			threadCode(i)
		}(i)
		i = i + 1
		continue
	}
	for dummy := true; ; {
		dummy = dummy
		continue
	}
}
