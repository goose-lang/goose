package goose

/*
Tests to demonstrate Go's behavior on various subtle examples.
*/

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func modifyArray(a [5]uint64) {
	a[0] = 1
}

func TestGoPassingArrayCopies(t *testing.T) {
	var a [5]uint64
	modifyArray(a)
	// arrays are values that are copied
	assert.Equal(t, [5]uint64{}, a)
}

type S struct {
	a uint64
	b uint32
	c bool
}

func (s *S) SetA() {
	s.a = 1
}

func (s S) GetA() uint64 {
	// this never modifies the callee's value
	s.a = 2
	return s.a
}

func TestGoUseStructMethodsOnValue(t *testing.T) {
	var s S
	s.SetA() // pointer method on value
	assert.Equal(t, uint64(1), s.a)
	assert.Equal(t, uint64(2), s.GetA())
	assert.Equal(t, uint64(1), s.a)
}

func TestGoUseStructMethodsOnPointer(t *testing.T) {
	s := &S{}
	s.SetA()
	assert.Equal(t, uint64(1), s.a)
	assert.Equal(t, uint64(2), s.GetA()) // value method on pointer
	assert.Equal(t, uint64(1), s.a)
}

type IntPair struct {
	b uint64
	a uint64
}

type withNext func(next func() uint64) interface{}

func initializeWith(body withNext) interface{} {
	index := uint64(0)
	next := func() uint64 {
		index++
		return index
	}
	return body(next)
}

func TestStructInitializedInProgramOrder(t *testing.T) {
	s1 := initializeWith(func(next func() uint64) interface{} {
		return IntPair{
			a: next(),
			b: next(),
		}
	})
	assert.Equal(t, IntPair{a: 1, b: 2}, s1)
	s2 := initializeWith(func(next func() uint64) interface{} {
		return IntPair{
			b: next(),
			a: next(),
		}
	})
	assert.Equal(t, IntPair{b: 1, a: 2}, s2)
}
