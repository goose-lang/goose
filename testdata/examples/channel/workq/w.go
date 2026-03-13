package workq

import (
	"strings"
	"sync/atomic"
)

type Worker struct {
	queue chan string
	steal chan chan *string // reply is a pointer: nil means nothing to steal
}

func (w *Worker) run(
	neighbor *Worker,
	total *atomic.Int64,
	remaining *atomic.Int64,
	done chan struct{},
) {
	for {
		select {
		case <-done:
			return

		case doc := <-w.queue:
			w.process(doc, total, remaining, done)

		case reply := <-w.steal:
			// A neighbor wants to steal a document from us.
			// Respond immediately: send a document if available, nil otherwise.
			select {
			case doc := <-w.queue:
				reply <- &doc
			default:
				reply <- nil
			}

		default:
			// Idle: attempt to steal from neighbor.
			// reply is buffered so the victim can always respond, even if
			// we find local work and stop listening before they reply.
			reply := make(chan *string, 1)
			select {
			case <-done:
				return
			case neighbor.steal <- reply:
				// Steal request accepted; wait for their response.
				if doc := <-reply; doc != nil {
					w.process(*doc, total, remaining, done)
				}
			case doc := <-w.queue:
				// New work arrived locally while we were trying to steal.
				w.process(doc, total, remaining, done)
			}
		}
	}
}

func (w *Worker) process(doc string, total *atomic.Int64, remaining *atomic.Int64, done chan struct{}) {
	total.Add(int64(len(strings.Fields(doc))))
	if remaining.Add(-1) == 0 {
		close(done)
	}
}

func wordCount(docs []string) int64 {
	if len(docs) == 0 {
		return 0
	}
	const numWorkers = 2
	workers := make([]*Worker, numWorkers)
	for i := range workers {
		workers[i] = &Worker{
			queue: make(chan string, len(docs)),
			steal: make(chan chan *string),
		}
	}

	// All documents start on worker 0's queue — maximally unbalanced.
	for _, doc := range docs {
		workers[0].queue <- doc
	}

	var total atomic.Int64
	var remaining atomic.Int64
	remaining.Store(int64(len(docs)))
	done := make(chan struct{})

	for i, w := range workers {
		neighbor := workers[(i+1)%numWorkers]
		go w.run(neighbor, &total, &remaining, done)
	}

	<-done
	return total.Load()
}
