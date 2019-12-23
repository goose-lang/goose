package unittest

import "sync"

func useLocks() {
	m := new(sync.RWMutex)
	m.Lock()
	m.Unlock()
}

func useCondVar() {
	m := new(sync.RWMutex)
	c := sync.NewCond(m)
	m.Lock()
	c.Signal()
	// NOTE: this example is artificial and deadlocks here
	c.Wait()
	m.Unlock()
}
