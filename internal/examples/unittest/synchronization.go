package unittest

import "sync"

// DoSomeLocking uses the entire lock API
func DoSomeLocking(l *sync.RWMutex) {
	l.Lock()
	l.Unlock()
	l.RLock()
	l.RLock()
	l.RUnlock()
	l.RUnlock()
}

func makeLock() {
	l := new(sync.RWMutex)
	DoSomeLocking(l)
}
