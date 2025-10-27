package chan_spec_raw_examples

// Extracted from Gobra at
// https://github.com/viperproject/gobra/blob/b573af1cfd79d624489a5f5846d9cc0b8eb83e17/src/test/resources/regressions/examples/evaluation/parallel_search_replace.gobra/
//
// Any copyright is dedicated to the Public Domain.
// http://creativecommons.org/publicdomain/zero/1.0/

import (
	"sync"

	"github.com/goose-lang/goose/model/channel"
)

func worker(c *channel.Channel[[]int], wg *sync.WaitGroup, x, y int) {
	for s, ok := c.Receive(); ok; s, ok = c.Receive() {
		for i := 0; i != len(s); i++ {
			if s[i] == x {
				s[i] = y
			}
		}
		wg.Done()
	}
}

func SearchReplace(s []int, x, y int) {
	if len(s) == 0 {
		return
	}
	workers := 8
	workRange := 1000
	c := channel.NewChannel[[]int](4)
	var wg sync.WaitGroup
	for i := 0; i != workers; i++ {
		go worker(c, &wg, x, y)
	}
	for offset := 0; offset != len(s); {
		nextOffset := offset + workRange
		if nextOffset > len(s) {
			nextOffset = len(s)
		}
		section := s[offset:nextOffset]
		wg.Add(1)
		c.Send(section)
		offset = nextOffset
	}
	wg.Wait()
}
