package unittest

type KVPair[K any, V any] struct {
	Key   K
	Value V
	Other NonGenericKVPair
}

type IndexedKVPair[K any, V any] struct {
	Key   K
	Value V
	Index uint64
}

type NonGenericKVPair struct {
	Key   uint64
	Value string
}

func testGenericStructs() uint64 {
	kv_pair_generic := KVPair[uint64, string]{}
	kv_pair_generic_ptr := KVPair[uint64, *uint64]{}
	kv_pair_partly_generic := IndexedKVPair[uint64, string]{}
	kv_pair_non_generic := NonGenericKVPair{}
	kv_pair_inner_generic := new(KVPair[uint64, KVPair[uint64, string]])
	kv_pair_inner_non_generic := KVPair[uint64, NonGenericKVPair]{}
	kv_pair_generic.Key = 1
	kv_pair_partly_generic.Value = "generic_val"
	kv_pair_non_generic.Key = 2
	kv_pair_inner_generic.Key = 3
	kv_pair_inner_generic.Value = kv_pair_generic
	kv_pair_inner_non_generic.Key = 4
	kv_pair_generic_ptr.Key = 0
	return kv_pair_inner_generic.Value.Key
}
