package unittest

import "sync"

func DoSomeLocking(l *sync.RWMutex) {
	l.Lock()
	l.Unlock()
	l.RLock()
	l.RLock()
	l.RUnlock()
	l.RUnlock()
}
