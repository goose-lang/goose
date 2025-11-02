package chan_spec_raw_examples

import (
	"fmt"
	"sync"
	"testing"
	"time"
)

func TestAsync(t *testing.T) {
	result := Async(func() string {
		return "hello"
	})

	select {
	case val := <-result:
		if val != "hello" {
			panic(fmt.Sprintf("Expected 'hello', got '%s'", val))
		}
	case <-time.After(100 * time.Millisecond):
		panic("Async timed out")
	}
}

func TestMapServer(t *testing.T) {
	s := mkStream(func(input string) string {
		return "processed-" + input
	})

	go MapServer(s)

	s.req <- "test"

	select {
	case result := <-s.res:
		if result != "processed-test" {
			panic(fmt.Sprintf("Expected 'processed-test', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("MapServer timed out")
	}

	close(s.req)
}

func TestMuxer(t *testing.T) {
	streamChan := make(chan stream)

	go Muxer(streamChan)

	// Create multiple streams
	s1 := mkStream(func(input string) string {
		return "s1-" + input
	})
	s2 := mkStream(func(input string) string {
		return "s2-" + input
	})

	streamChan <- s1
	streamChan <- s2

	// Test first stream
	s1.req <- "test1"
	select {
	case result := <-s1.res:
		if result != "s1-test1" {
			panic(fmt.Sprintf("Expected 's1-test1', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("Muxer stream 1 timed out")
	}

	// Test second stream
	s2.req <- "test2"
	select {
	case result := <-s2.res:
		if result != "s2-test2" {
			panic(fmt.Sprintf("Expected 's2-test2', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("Muxer stream 2 timed out")
	}

	close(s1.req)
	close(s2.req)
	close(streamChan)
}

func TestCancellableMuxer(t *testing.T) {
	streamChan := make(chan stream)
	done := make(chan struct{})

	go CancellableMuxer(streamChan, done)

	s := mkStream(func(input string) string {
		return "result-" + input
	})

	streamChan <- s

	// Verify it works before cancellation
	s.req <- "test"
	select {
	case result := <-s.res:
		if result != "result-test" {
			panic(fmt.Sprintf("Expected 'result-test', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("CancellableMuxer timed out before cancellation")
	}

	// Cancel the muxer
	close(done)
	time.Sleep(10 * time.Millisecond) // Give it time to shutdown

	// The muxer should have stopped, but existing streams should still work
	// since MapServer is already running
	s.req <- "test2"
	select {
	case result := <-s.res:
		if result != "result-test2" {
			panic(fmt.Sprintf("Expected 'result-test2', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("Existing stream timed out after cancellation")
	}

	close(s.req)
	close(streamChan)
}

func TestMuxerConcurrent(t *testing.T) {
	streamChan := make(chan stream, 10)

	go Muxer(streamChan)

	const numStreams = 10
	streams := make([]stream, numStreams)

	// Create and send multiple streams
	for i := 0; i < numStreams; i++ {
		idx := i
		streams[i] = mkStream(func(input string) string {
			return fmt.Sprintf("stream%d-%s", idx, input)
		})
		streamChan <- streams[i]
	}

	// Send requests to all streams concurrently
	var wg sync.WaitGroup
	wg.Add(numStreams)

	for i := 0; i < numStreams; i++ {
		go func(idx int) {
			defer wg.Done()
			streams[idx].req <- "data"

			select {
			case result := <-streams[idx].res:
				expected := fmt.Sprintf("stream%d-data", idx)
				if result != expected {
					panic(fmt.Sprintf("Stream %d: expected '%s', got '%s'", idx, expected, result))
				}
			case <-time.After(100 * time.Millisecond):
				panic(fmt.Sprintf("Stream %d timed out", idx))
			}

			close(streams[idx].req)
		}(i)
	}

	wg.Wait()
	close(streamChan)
}
