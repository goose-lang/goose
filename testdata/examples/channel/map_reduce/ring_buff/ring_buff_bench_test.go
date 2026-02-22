package ring

import (
	"bytes"
	"slices"
	"testing"
)

type KV struct {
	Partition uint32
	Key       []byte
	Val       []byte
}

type RunItem struct {
	Run   *Run
	Slots []*Slot // must be held until Run is fully consumed
}

// ----- helpers (same as before, self-contained) -----

func upperBoundedKey(b []byte, keyLen int) []byte {
	if len(b) > keyLen {
		return b[:keyLen]
	}
	return b
}

type xorshift64 struct{ x uint64 }

func (r *xorshift64) next() uint64 {
	x := r.x
	x ^= x >> 12
	x ^= x << 25
	x ^= x >> 27
	r.x = x
	return x * 2685821657736338717
}

func hash32FNV1a(b []byte) uint32 {
	var h uint32 = 2166136261
	for _, c := range b {
		h ^= uint32(c)
		h *= 16777619
	}
	return h
}

func partitionOfKey(key []byte, numPartitions uint32) uint32 {
	return hash32FNV1a(key) % numPartitions
}

func fillRecord(dst []byte, keyLen, valLen int, rng *xorshift64) []byte {
	n := keyLen + valLen
	if cap(dst) < n {
		dst = make([]byte, n)
	} else {
		dst = dst[:n]
	}
	for i := 0; i < n; i++ {
		dst[i] = byte(rng.next())
	}
	return dst
}

// mergeSlotsBytes mirrors MergeSlots but avoids records.Codec[K,V].
// Sort key: (Partition, key bytes).
func mergeSlotsBytes(slots []*Slot, keyLen int) *Run {
	total := 0
	for _, s := range slots {
		total += len(s.Sidecar)
	}

	all := make([]Ref, 0, total)
	for _, s := range slots {
		all = append(all, s.Sidecar...)
	}

	slices.SortFunc(all, func(a, b Ref) int {
		if a.Partition < b.Partition {
			return -1
		}
		if a.Partition > b.Partition {
			return 1
		}
		ka := upperBoundedKey(a.Data, keyLen)
		kb := upperBoundedKey(b.Data, keyLen)
		return bytes.Compare(ka, kb)
	})

	return &Run{Refs: all}
}

func sortKVsInPlace(kvs []KV) {
	slices.SortFunc(kvs, func(a, b KV) int {
		if a.Partition < b.Partition {
			return -1
		}
		if a.Partition > b.Partition {
			return 1
		}
		return bytes.Compare(a.Key, b.Key)
	})
}

// writer consumes run refs (pointing into slots) and writes deterministic bytes to sink.
// Then it releases the held slots.
func writeRunAndRelease(sink *bytes.Buffer, item RunItem, keyLen int, rb *RingBuffer) {
	for _, ref := range item.Run.Refs {
		d := ref.Data
		key := d[:keyLen]
		val := d[keyLen:]
		// “Write” key and val to sink; could also encode partition if you want.
		_, _ = sink.Write(key)
		_, _ = sink.Write(val)
	}
	for _, s := range item.Slots {
		s.Reset()
		rb.free <- s
	}
}

// ----- Benchmark 1: Ring slots -> merge/sort into Run -> writer holds slots until done -----

func BenchmarkPipeline_RingSlotsSortRunWrite(b *testing.B) {
	b.ReportAllocs()

	const (
		numSlots       = 256
		slotCap        = 32 * 1024
		sidecarCapHint = 512

		recordsPerIter = 200_000

		keyLen = 16
		valMin = 24
		valMax = 200

		numPartitions = 128
		slotsPerRun   = 4
	)

	rb := New(numSlots, slotCap, sidecarCapHint)

	// Pre-size sink roughly: bytes written per record = keyLen+valLen.
	// We’ll just grow generously per iteration to reduce sink realloc noise.
	approxBytesPerRec := keyLen + ((valMin + valMax) / 2)

	for it := 0; it < b.N; it++ {
		runs := make(chan RunItem, 16)

		doneWriter := make(chan struct{})
		go func() {
			defer close(doneWriter)
			var sink bytes.Buffer
			sink.Grow(recordsPerIter * approxBytesPerRec)

			for item := range runs {
				writeRunAndRelease(&sink, item, keyLen, rb)
			}

			// prevent compiler DCE
			if sink.Len() == 123456789 {
				b.Fatalf("impossible")
			}
		}()

		// Merger goroutine: receive slots, group into runs, sort, emit RunItem.
		doneMerger := make(chan struct{})
		go func() {
			defer close(doneMerger)
			runSlots := make([]*Slot, 0, slotsPerRun)

			flushRun := func() {
				if len(runSlots) == 0 {
					return
				}
				run := mergeSlotsBytes(runSlots, keyLen)

				held := make([]*Slot, len(runSlots))
				copy(held, runSlots)
				runs <- RunItem{Run: run, Slots: held}

				runSlots = runSlots[:0]
			}

			for {
				s := <-rb.data
				if s == nil {
					flushRun()
					close(runs)
					return
				}
				runSlots = append(runSlots, s)
				if len(runSlots) == slotsPerRun {
					flushRun()
				}
			}
		}()

		// Producer: pack records into slots and send to rb.Data().
		doneProducer := make(chan struct{})
		go func() {
			defer close(doneProducer)
			var rng xorshift64
			rng.x = 0xC0FFEE + uint64(it)

			slot := <-rb.free
			slot.Reset()

			var rec []byte
			for i := 0; i < recordsPerIter; i++ {
				valLen := int(valMin + (rng.next() % uint64(valMax-valMin+1)))
				rec = fillRecord(rec[:0], keyLen, valLen, &rng)
				part := partitionOfKey(rec[:keyLen], numPartitions)

				if len(rec) > slot.Remaining() {
					rb.data <- slot
					slot = <-rb.free
					slot.Reset()
				}
				if !slot.Append(part, rec) {
					// Shouldn't happen with chosen params.
					rb.data <- slot
					rb.data <- nil
					return
				}
			}

			if slot.End > 0 {
				rb.data <- slot
			} else {
				rb.free <- slot
			}
			rb.data <- nil
		}()

		<-doneProducer
		<-doneMerger
		<-doneWriter
	}
}

// ----- Benchmark 2: Naive: receive KV, collect all, sort, output to another KV channel -----

func BenchmarkPipeline_NaiveKVCollectSortEmit(b *testing.B) {
	b.ReportAllocs()

	const (
		recordsPerIter = 200_000

		keyLen = 16
		valMin = 24
		valMax = 200

		numPartitions = 128
	)

	approxBytesPerRec := keyLen + ((valMin + valMax) / 2)

	for it := 0; it < b.N; it++ {
		in := make(chan KV, 1024)
		out := make(chan KV, 1024)

		// Writer: consumes sorted KV and writes to bytes.Buffer.
		doneWriter := make(chan struct{})
		go func() {
			defer close(doneWriter)
			var sink bytes.Buffer
			sink.Grow(recordsPerIter * approxBytesPerRec)
			for kv := range out {
				_, _ = sink.Write(kv.Key)
				_, _ = sink.Write(kv.Val)
			}
			if sink.Len() == 123456789 {
				b.Fatalf("impossible")
			}
		}()

		// Sort stage: collect, sort, emit.
		doneSorter := make(chan struct{})
		go func() {
			defer close(doneSorter)
			kvs := make([]KV, 0, recordsPerIter)
			for kv := range in {
				kvs = append(kvs, kv)
			}
			sortKVsInPlace(kvs)
			for _, kv := range kvs {
				out <- kv
			}
			close(out)
		}()

		// Producer: generate and send KV (allocates per record).
		var rng xorshift64
		rng.x = 0xC0FFEE + uint64(it)

		for i := 0; i < recordsPerIter; i++ {
			valLen := int(valMin + (rng.next() % uint64(valMax-valMin+1)))
			rec := fillRecord(nil, keyLen, valLen, &rng) // alloc per record
			part := partitionOfKey(rec[:keyLen], numPartitions)
			in <- KV{
				Partition: part,
				Key:       rec[:keyLen],
				Val:       rec[keyLen:],
			}
		}
		close(in)

		<-doneSorter
		<-doneWriter
	}
}
