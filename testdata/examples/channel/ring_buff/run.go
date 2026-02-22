package ring

import (
	"slices"

	"github.com/goose-lang/goose/testdata/examples/channel/records"
)

// -------------------- Run --------------------

// Run is the sorted output of merging n consecutive slots. Refs is the
// globally sorted sidecar; each Ref.Data points directly into its source
// slot's buffer, so the slots must not be released until the Run is consumed.
type Run struct {
	Refs []Ref
}

// MergeSlots collects all refs from slots, sorts them by (Partition, key
// bytes), and returns a Run. codec.Compare drives the within-partition
// ordering. No data is copied — Ref.Data points into the original slot buffers.
func MergeSlots[K, V any](slots []*Slot, codec records.Codec[K, V]) *Run {
	total := 0
	for _, s := range slots {
		total += len(s.Sidecar)
	}

	all := make([]Ref, 0, total)
	for _, s := range slots {
		all = append(all, s.Sidecar...)
	}

	slices.SortFunc(all, func(a, b Ref) int {
		// Partition is int: avoid cmp.Compare dependency.
		if a.Partition < b.Partition {
			return -1
		}
		if a.Partition > b.Partition {
			return 1
		}
		return codec.Compare(a.Data, b.Data)
	})

	return &Run{Refs: all}
}
