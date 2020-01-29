package goose_test

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

func mkNext() func() uint64 {
	index := uint64(0)
	next := func() uint64 {
		index++
		return index
	}
	return next
}

func TestNextHelper(t *testing.T) {
	next := mkNext()
	assert.Equal(t, uint64(1), next())
	assert.Equal(t, uint64(2), next())
	assert.Equal(t, uint64(3), next())
}

func TestStructInitializedInProgramOrder(t *testing.T) {
	next := mkNext()
	s1 := IntPair{
		a: next(),
		b: next(),
	}
	assert.Equal(t, IntPair{a: 1, b: 2}, s1)
	next = mkNext()
	s2 := IntPair{
		b: next(),
		a: next(),
	}
	assert.Equal(t, IntPair{b: 1, a: 2}, s2)
}

// each defined type (types.Named) creates a distinct type at runtime,
// detectable via interface type casts or type switches
type type1 uint64
type type2 uint64

func TestInterfaceTypeIdentity(t *testing.T) {
	assert := assert.New(t)
	var isUint64 interface{} = uint64(3)
	var isType1 interface{} = type1(3)
	var ok bool
	_, ok = isUint64.(uint64)
	assert.Equal(true, ok, "uint64->uint64 check")
	_, ok = isUint64.(type1)
	assert.Equal(false, ok, "uint64 should not be type1")

	_, ok = isType1.(type1)
	assert.Equal(true, ok, "isType1->isType1 check")
	_, ok = isType1.(uint64)
	assert.Equal(false, ok, "type1 should not be uint64")
	_, ok = isType1.(type2)
	assert.Equal(false, ok, "type1 should not be type2")
}
