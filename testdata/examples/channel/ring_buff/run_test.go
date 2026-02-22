package ring

import (
	"testing"

	"github.com/goose-lang/goose/testdata/examples/channel/records"
)

// helpers

func makeSlotWithRecords(cap int, entries []struct {
	partition uint32
	data      []byte
}) *Slot {
	s := makeSlot(cap)
	for _, e := range entries {
		s.Append(e.partition, e.data)
	}
	return s
}

func refStrings(run *Run) []string {
	out := make([]string, len(run.Refs))
	for i, r := range run.Refs {
		out[i] = string(r.Data)
	}
	return out
}

func refPartitions(run *Run) []uint32 {
	out := make([]uint32, len(run.Refs))
	for i, r := range run.Refs {
		out[i] = r.Partition
	}
	return out
}

// tests

func TestMergeSlots_Empty(t *testing.T) {
	run := MergeSlots([]*Slot{makeSlot(16)}, records.WordCountCodec{})
	if len(run.Refs) != 0 {
		t.Fatalf("expected 0 refs, got %d", len(run.Refs))
	}
}

func TestMergeSlots_SingleSlot_SortedByKey(t *testing.T) {
	codec := records.WordCountCodec{}
	s := makeSlot(128)
	s.Append(0, codec.Marshal(nil, "banana", 1))
	s.Append(0, codec.Marshal(nil, "apple", 1))
	s.Append(0, codec.Marshal(nil, "cherry", 1))

	run := MergeSlots([]*Slot{s}, codec)

	keys := refStrings(run) // raw bytes, compare via codec
	for i := 0; i < len(run.Refs)-1; i++ {
		if codec.Compare(run.Refs[i].Data, run.Refs[i+1].Data) > 0 {
			t.Errorf("refs not sorted at index %d and %d", i, i+1)
		}
	}
	_ = keys
}

func TestMergeSlots_SortedByPartitionFirst(t *testing.T) {
	codec := records.WordCountCodec{}
	s1 := makeSlot(128)
	s1.Append(2, codec.Marshal(nil, "apple", 1))
	s1.Append(0, codec.Marshal(nil, "zebra", 1))

	s2 := makeSlot(128)
	s2.Append(1, codec.Marshal(nil, "mango", 1))

	run := MergeSlots([]*Slot{s1, s2}, codec)

	partitions := refPartitions(run)
	for i := 0; i < len(partitions)-1; i++ {
		if partitions[i] > partitions[i+1] {
			t.Errorf("partitions not sorted at index %d: %v", i, partitions)
		}
	}
}

func TestMergeSlots_WithinPartition_SortedByKey(t *testing.T) {
	codec := records.WordCountCodec{}
	s1 := makeSlot(128)
	s1.Append(1, codec.Marshal(nil, "zebra", 1))
	s1.Append(1, codec.Marshal(nil, "apple", 1))

	s2 := makeSlot(128)
	s2.Append(1, codec.Marshal(nil, "mango", 1))

	run := MergeSlots([]*Slot{s1, s2}, codec)

	for i := 0; i < len(run.Refs)-1; i++ {
		a, b := run.Refs[i], run.Refs[i+1]
		if a.Partition == b.Partition && codec.Compare(a.Data, b.Data) > 0 {
			t.Errorf("within partition %d: records not sorted at index %d", a.Partition, i)
		}
	}
}

func TestMergeSlots_RefsPointIntoOriginalBuffers(t *testing.T) {
	codec := records.WordCountCodec{}
	s := makeSlot(128)
	rec := codec.Marshal(nil, "hello", 1)
	s.Append(0, rec)

	run := MergeSlots([]*Slot{s}, codec)

	// Mutate the slot's backing buffer and verify the ref sees the change.
	s.Data[2] = 'H'
	if run.Refs[0].Data[2] != 'H' {
		t.Fatal("Run.Refs should point into the original slot buffer, not a copy")
	}
}

func TestMergeSlots_MultipleSlots_TotalRefCount(t *testing.T) {
	codec := records.WordCountCodec{}
	s1 := makeSlot(128)
	s1.Append(0, codec.Marshal(nil, "a", 1))
	s1.Append(0, codec.Marshal(nil, "b", 1))

	s2 := makeSlot(128)
	s2.Append(1, codec.Marshal(nil, "c", 1))

	run := MergeSlots([]*Slot{s1, s2}, codec)

	if len(run.Refs) != 3 {
		t.Fatalf("expected 3 refs, got %d", len(run.Refs))
	}
}
