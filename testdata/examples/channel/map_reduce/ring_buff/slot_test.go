package ring

import (
	"testing"
)

func makeSlot(cap int) *Slot {
	return &Slot{
		Data:    make([]byte, cap),
		Sidecar: make([]Ref, 0, 8),
	}
}

func TestAppend_Basic(t *testing.T) {
	s := makeSlot(16)
	data := []byte("hello")

	if !s.Append(1, data) {
		t.Fatal("expected Append to succeed")
	}

	if s.End != 5 {
		t.Fatalf("expected End=5, got %d", s.End)
	}
	if len(s.Sidecar) != 1 {
		t.Fatalf("expected 1 sidecar entry, got %d", len(s.Sidecar))
	}
	if s.Sidecar[0].Partition != 1 {
		t.Fatalf("expected partition=1, got %d", s.Sidecar[0].Partition)
	}
	if string(s.Sidecar[0].Data) != "hello" {
		t.Fatalf("expected Data='hello', got %q", s.Sidecar[0].Data)
	}
}

func TestAppend_Multiple(t *testing.T) {
	s := makeSlot(16)

	s.Append(0, []byte("foo"))
	s.Append(1, []byte("bar"))

	if s.End != 6 {
		t.Fatalf("expected End=6, got %d", s.End)
	}
	if string(s.Sidecar[0].Data) != "foo" {
		t.Errorf("expected first record 'foo', got %q", s.Sidecar[0].Data)
	}
	if string(s.Sidecar[1].Data) != "bar" {
		t.Errorf("expected second record 'bar', got %q", s.Sidecar[1].Data)
	}
}

func TestAppend_DoesNotFit(t *testing.T) {
	s := makeSlot(4)

	if !s.Append(0, []byte("fits")) {
		t.Fatal("expected first Append to succeed")
	}
	if s.Append(0, []byte("x")) {
		t.Fatal("expected Append to fail when full")
	}
	// State must be unchanged.
	if s.End != 4 {
		t.Fatalf("expected End=4 after failed Append, got %d", s.End)
	}
	if len(s.Sidecar) != 1 {
		t.Fatalf("expected sidecar unchanged, got %d entries", len(s.Sidecar))
	}
}

func TestAppend_RefPointsIntoData(t *testing.T) {
	s := makeSlot(16)
	s.Append(0, []byte("hello"))

	// Mutate the backing buffer and verify the ref sees the change.
	s.Data[0] = 'H'
	if s.Sidecar[0].Data[0] != 'H' {
		t.Fatal("Ref.Data should be a subslice of the backing buffer, not a copy")
	}
}

func TestReset(t *testing.T) {
	s := makeSlot(16)
	s.Append(0, []byte("hello"))
	s.Reset()

	if s.End != 0 {
		t.Fatalf("expected End=0 after Reset, got %d", s.End)
	}
	if len(s.Sidecar) != 0 {
		t.Fatalf("expected empty Sidecar after Reset, got %d entries", len(s.Sidecar))
	}
}

func TestRemaining(t *testing.T) {
	s := makeSlot(10)
	if s.Remaining() != 10 {
		t.Fatalf("expected Remaining=10, got %d", s.Remaining())
	}
	s.Append(0, []byte("hello"))
	if s.Remaining() != 5 {
		t.Fatalf("expected Remaining=5, got %d", s.Remaining())
	}
}

func TestAppend_ExactFit(t *testing.T) {
	s := makeSlot(5)
	if !s.Append(0, []byte("hello")) {
		t.Fatal("expected exact-fit Append to succeed")
	}
	if s.Remaining() != 0 {
		t.Fatalf("expected Remaining=0, got %d", s.Remaining())
	}
}
