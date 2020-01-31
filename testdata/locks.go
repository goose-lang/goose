package example

import "sync"

type hasJustCondVar struct {
	cond sync.Cond // ERROR sync.Cond
}
type hasJustMutex struct {
	m sync.Mutex // ERROR sync.Mutex
}
