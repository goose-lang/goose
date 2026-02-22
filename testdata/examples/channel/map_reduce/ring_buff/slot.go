package ring

// -------------------- Slot --------------------

// Ref is a sidecar entry describing one encoded record inside a slot payload.
type Ref struct {
	// The partition assignment from the hash of the record
	Partition uint32
	// A pointer to the record in the source slot's Data buffer
	Data []byte
}

// Slot is a fixed-capacity byte buffer paired with sidecar metadata. Records
// are packed consecutively into Data, and each record's partition and a direct
// pointer into its bytes are tracked in Sidecar. End marks the write cursor —
// the boundary between written and unwritten bytes.
type Slot struct {
	// Records stored consecutively
	Data []byte
	// Write cursor: first unwritten byte
	End uint32
	// One entry per record, in write order
	Sidecar []Ref
}

// Reset clears the slot for reuse without reallocating.
func (s *Slot) Reset() {
	s.End = 0
	s.Sidecar = s.Sidecar[:0]
}

// Append writes p into the slot's data buffer, records a Ref with the given
// partition, and advances End. Returns false (and makes no change) if p does
// not fit in the remaining capacity.
func (s *Slot) Append(partition uint32, p []byte) bool {
	start := s.End
	end := start + uint32(len(p))
	if int(end) > len(s.Data) {
		return false
	}
	copy(s.Data[start:end], p)
	s.Sidecar = append(s.Sidecar, Ref{
		Partition: partition,
		Data:      s.Data[start:end],
	})
	s.End = end
	return true
}

// Remaining returns how many bytes are still available in the slot.
func (s *Slot) Remaining() int {
	return len(s.Data) - int(s.End)
}

func NewSlot(cap int) *Slot {
	return &Slot{
		Data:    make([]byte, cap),
		Sidecar: make([]Ref, 0, 8),
	}
}
