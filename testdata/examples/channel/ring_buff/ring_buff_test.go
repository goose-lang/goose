package ring

import (
	"testing"
	"unsafe"
)

func TestNew_PanicsOnZeroSlots(t *testing.T) {
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("expected panic for numSlots=0")
		}
	}()
	New(0, 64, 8)
}

func TestNew_FreeChannelPrimed(t *testing.T) {
	rb := New(4, 64, 8)
	if len(rb.Free()) != 4 {
		t.Fatalf("expected 4 free slots, got %d", len(rb.Free()))
	}
	if len(rb.Data()) != 0 {
		t.Fatalf("expected 0 data slots, got %d", len(rb.Data()))
	}
}

func TestNew_SlotCapacities(t *testing.T) {
	rb := New(3, 64, 8)
	for i := 0; i < 3; i++ {
		s := <-rb.Free()
		if cap(s.Data) != 64 {
			t.Errorf("slot %d: expected Data cap=64, got %d", i, cap(s.Data))
		}
		if cap(s.Sidecar) != 8 {
			t.Errorf("slot %d: expected Sidecar cap=8, got %d", i, cap(s.Sidecar))
		}
	}
}

func TestNew_ContiguousBackingArray(t *testing.T) {
	rb := New(3, 64, 8)
	slots := make([]*Slot, 3)
	for i := range slots {
		slots[i] = <-rb.Free()
	}
	for i := 1; i < len(slots); i++ {
		a := uintptr(unsafe.Pointer(unsafe.SliceData(slots[i-1].Data)))
		b := uintptr(unsafe.Pointer(unsafe.SliceData(slots[i].Data)))
		if b-a != 64 {
			t.Errorf("slots %d and %d are not contiguous: diff=%d", i-1, i, b-a)
		}
	}
}

func TestSlotCap(t *testing.T) {
	rb := New(2, 128, 8)
	if rb.SlotCap() != 128 {
		t.Fatalf("expected SlotCap=128, got %d", rb.SlotCap())
	}
}

func TestRingBuffer_ProducerConsumer(t *testing.T) {
	rb := New(2, 64, 8)

	// Producer: acquire, populate, send.
	s := <-rb.Free()
	s.Reset()
	s.Append(0, []byte("hello"))
	rb.Data() <- s

	// Consumer: receive, verify, return.
	got := <-rb.Data()
	if string(got.Sidecar[0].Data) != "hello" {
		t.Fatalf("expected 'hello', got %q", got.Sidecar[0].Data)
	}
	got.Reset()
	rb.Free() <- got

	// Slot should be back in the free pool.
	if len(rb.Free()) != 2 {
		t.Fatalf("expected 2 free slots after release, got %d", len(rb.Free()))
	}
}

func TestRingBuffer_Close(t *testing.T) {
	rb := New(2, 64, 8)
	close(rb.Data())

	_, ok := <-rb.Data()
	if ok {
		t.Fatal("expected ok=false after close")
	}
}

func TestRingBuffer_SlotsReusable(t *testing.T) {
	rb := New(1, 64, 8)

	for i := 0; i < 3; i++ {
		s := <-rb.Free()
		s.Reset()
		s.Append(0, []byte("round"))
		rb.Data() <- s

		got := <-rb.Data()
		if string(got.Sidecar[0].Data) != "round" {
			t.Fatalf("iteration %d: expected 'round', got %q", i, got.Sidecar[0].Data)
		}
		got.Reset()
		rb.Free() <- got
	}
}
