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

// buffer_size = 0 is an unbuffered channel
func NewKVPair[K any, V any](Key K, Value V) KVPair[K, V] {
	return KVPair[K, V]{
		Key:   Key,
		Value: Value,
	}
}

// buffer_size = 0 is an unbuffered channel
func NewKVPairRef[K any, V any](Key K, Value V) *KVPair[K, V] {
	return &KVPair[K, V]{
		Key:   Key,
		Value: Value,
	}
}

func (c *KVPair[K, V]) GetKey() K {
	return c.Key
}
func (c *KVPair[K, V]) GetValue() V {
	return c.Value
}

func testGenericStructs() uint64 {
	kv_pair_generic_define_inline := KVPair[uint64, string]{}
	kv_pair_generic_from_func := NewKVPair[uint64, string](0, "str")
	kv_pair_generic_ptr := KVPair[uint64, *uint64]{}
	kv_pair_partly_generic := IndexedKVPair[uint64, string]{}
	kv_pair_non_generic := NonGenericKVPair{}
	kv_pair_inner_generic := new(KVPair[uint64, KVPair[uint64, string]])
	kv_pair_inner_non_generic := KVPair[uint64, NonGenericKVPair]{}
	kv_pair_generic_define_inline.Key = 1
	kv_pair_partly_generic.Value = kv_pair_generic_from_func.GetValue()
	kv_pair_non_generic.Key = *kv_pair_generic_ptr.GetValue()
	kv_pair_inner_generic.Key = 3
	kv_pair_inner_generic.Value = kv_pair_generic_from_func
	kv_pair_inner_non_generic.Key = 4
	kv_pair_generic_ptr.Key = kv_pair_generic_define_inline.GetKey()
	return kv_pair_inner_generic.Value.Key
}
