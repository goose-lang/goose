package machine

import "sync"

var wg sync.WaitGroup

func Spawn(f func()) {
	wg.Add(1)
	go func() {
		defer wg.Done()
		f()
	}()
}

func WaitForAllThreads() {
	wg.Wait()
}
