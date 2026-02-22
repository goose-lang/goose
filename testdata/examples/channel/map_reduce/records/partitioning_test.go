package records

import (
	"testing"
)

func TestSumHash_Empty(t *testing.T) {
	if SumHash([]byte{}) != 0 {
		t.Fatal("expected SumHash of empty input to be 0")
	}
}

func TestSumHash_SingleByte(t *testing.T) {
	if SumHash([]byte{42}) != 42 {
		t.Fatalf("expected SumHash({42})=42, got %d", SumHash([]byte{42}))
	}
}

func TestSumHash_Deterministic(t *testing.T) {
	key := []byte("hello")
	if SumHash(key) != SumHash(key) {
		t.Fatal("SumHash should be deterministic")
	}
}

func TestSumHash_OrderDependent(t *testing.T) {
	// SumHash is order-independent (it's addition), so "ab" and "ba" collide.
	// This test documents that known property rather than asserting it shouldn't happen.
	ab := SumHash([]byte("ab"))
	ba := SumHash([]byte("ba"))
	if ab != ba {
		t.Fatalf("SumHash should be order-independent: 'ab'=%d, 'ba'=%d", ab, ba)
	}
}

func TestPartition_InRange(t *testing.T) {
	keys := [][]byte{
		[]byte("hello"),
		[]byte("world"),
		[]byte("foo"),
		[]byte(""),
	}
	n := uint32(8)
	for _, k := range keys {
		p := Partition(k, n, SumHash)
		if p >= n {
			t.Errorf("Partition(%q, %d) = %d, want < %d", k, n, p, n)
		}
	}
}

func TestPartition_Deterministic(t *testing.T) {
	key := []byte("hello")
	if Partition(key, 8, SumHash) != Partition(key, 8, SumHash) {
		t.Fatal("Partition should be deterministic")
	}
}

func TestPartition_SinglePartition(t *testing.T) {
	// With n=1 every key must map to partition 0.
	keys := [][]byte{[]byte("a"), []byte("b"), []byte("hello")}
	for _, k := range keys {
		if p := Partition(k, 1, SumHash); p != 0 {
			t.Errorf("Partition(%q, 1) = %d, want 0", k, p)
		}
	}
}

func TestPartition_CustomHash(t *testing.T) {
	// A hash that always returns 5 should always map to 5 % n.
	constant := HashFn(func(_ []byte) uint32 { return 5 })
	if p := Partition([]byte("anything"), 4, constant); p != 1 {
		t.Errorf("expected partition=1 (5%%4), got %d", p)
	}
}
