package ring

// -------------------- Ring Buffer --------------------

// RingBuffer manages ownership of slots of records. The purpose is to write
// data into consecutive blocks so that processing can be done with spatial
// locality.
//
// Usage:
//
//	Producer:
//	  - Receive from Free(), call slot.Reset(), populate, then send to Data()
//	  - Close Data() when no more slots will be sent
//
//	Consumer:
//	  - Receive from Data(); ok=false means the ring is drained
//	  - After processing, send the slot back to Free()
//
// Both channels are exposed so callers can use them in select statements.
type RingBuffer struct {
	data    chan *Slot
	free    chan *Slot
	slotCap int
}

// New allocates a RingBuffer with numSlots slots. All slot data is backed by a
// single contiguous []byte allocation and all sidecar metadata by a single
// contiguous []Ref allocation so that the working set is compact.
func New(numSlots, slotCap, sidecarCapHint int) *RingBuffer {
	if numSlots <= 0 {
		panic("numSlots must be > 0")
	}
	allData := make([]byte, numSlots*slotCap)
	allMeta := make([]Ref, numSlots*sidecarCapHint)

	r := &RingBuffer{
		free:    make(chan *Slot, numSlots),
		data:    make(chan *Slot, numSlots),
		slotCap: slotCap,
	}

	for i := 0; i < numSlots; i++ {
		lo := i * slotCap
		hi := lo + slotCap
		lom := i * sidecarCapHint
		him := lom + sidecarCapHint
		r.free <- &Slot{
			Data:    allData[lo:hi:hi],
			Sidecar: allMeta[lom:him:him],
		}
	}
	return r
}

func (r *RingBuffer) SlotCap() int { return r.slotCap }

// Free is the channel of available slots. Producers receive from this,
// call slot.Reset(), populate the slot, then send it to Data().
func (r *RingBuffer) Free() chan *Slot { return r.free }

// Data is the channel of populated slots. Consumers receive from this,
// process the slot, then send it back to Free(). The producer closes
// this channel when no more slots will be sent.
func (r *RingBuffer) Data() chan *Slot { return r.data }
