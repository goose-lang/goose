package records

import (
	"testing"
)

var codec = WordCountCodec{}

func marshal(k string, v uint32) []byte {
	return codec.Marshal(nil, k, v)
}

// -------------------- Size --------------------

func TestSize(t *testing.T) {
	if got := codec.Size("hello", 1); got != wcLenSize+5+wcValSize {
		t.Fatalf("expected %d, got %d", wcLenSize+5+wcValSize, got)
	}
}

func TestSize_EmptyKey(t *testing.T) {
	if got := codec.Size("", 0); got != wcLenSize+wcValSize {
		t.Fatalf("expected %d, got %d", wcLenSize+wcValSize, got)
	}
}

// -------------------- Marshal / Unmarshal roundtrip --------------------

func TestMarshalUnmarshal_Roundtrip(t *testing.T) {
	cases := []struct {
		k string
		v uint32
	}{
		{"hello", 1},
		{"", 0},
		{"world", 99999},
		{"unicode: 日本語", 42},
	}
	for _, c := range cases {
		src := marshal(c.k, c.v)
		k, v, err := codec.Unmarshal(src)
		if err != nil {
			t.Errorf("Unmarshal(%q, %d): unexpected error: %v", c.k, c.v, err)
		}
		if k != c.k || v != c.v {
			t.Errorf("roundtrip: got (%q, %d), want (%q, %d)", k, v, c.k, c.v)
		}
	}
}

/*func TestUnmarshal_InvalidUTF8(t *testing.T) {
	// Build a record with a manually crafted invalid UTF-8 key.
	src := codec.Marshal(nil, "xx", 1)
	src[wcLenSize] = 0xff // corrupt first byte of key
	_, _, err := codec.Unmarshal(src)
	if err == nil {
		t.Fatal("expected error for invalid UTF-8 key")
	}
}*/

// -------------------- MarshalKey / MarshalVal --------------------

func TestMarshalKey(t *testing.T) {
	got := codec.MarshalKey(nil, "hello")
	if string(got) != "hello" {
		t.Fatalf("MarshalKey: expected 'hello', got %q", got)
	}
}

func TestMarshalVal(t *testing.T) {
	got := codec.MarshalVal(nil, 42)
	if len(got) != wcValSize {
		t.Fatalf("MarshalVal: expected %d bytes, got %d", wcValSize, len(got))
	}
	// Roundtrip through MarshalVal is implicit via Marshal/Unmarshal tests.
}

func TestMarshalAppends(t *testing.T) {
	dst := []byte("prefix")
	got := codec.Marshal(dst, "hi", 1)
	if string(got[:6]) != "prefix" {
		t.Fatal("Marshal should append, not overwrite dst")
	}
}

// -------------------- KeyBytes --------------------

func TestKeyBytes(t *testing.T) {
	src := marshal("hello", 99)
	kb := codec.KeyBytes(src)
	if string(kb) != "hello" {
		t.Fatalf("KeyBytes: expected 'hello', got %q", kb)
	}
}

func TestKeyBytes_PointsIntoSrc(t *testing.T) {
	src := marshal("hello", 1)
	kb := codec.KeyBytes(src)
	src[wcLenSize] = 'H'
	if kb[0] != 'H' {
		t.Fatal("KeyBytes should return a subslice of src, not a copy")
	}
}

func TestKeyBytes_EmptyKey(t *testing.T) {
	src := marshal("", 1)
	if len(codec.KeyBytes(src)) != 0 {
		t.Fatal("expected empty KeyBytes for empty key")
	}
}

// -------------------- Compare --------------------

func TestCompare_Equal(t *testing.T) {
	a := marshal("hello", 1)
	b := marshal("hello", 2) // same key, different value
	if codec.Compare(a, b) != 0 {
		t.Fatal("expected Compare to return 0 for equal keys")
	}
}

func TestCompare_Less(t *testing.T) {
	a := marshal("apple", 1)
	b := marshal("banana", 1)
	if codec.Compare(a, b) >= 0 {
		t.Fatal("expected apple < banana")
	}
}

func TestCompare_Greater(t *testing.T) {
	a := marshal("zebra", 1)
	b := marshal("apple", 1)
	if codec.Compare(a, b) <= 0 {
		t.Fatal("expected zebra > apple")
	}
}

func TestCompare_LexicographicNotLength(t *testing.T) {
	// "b" > "aa" lexicographically even though "aa" is longer.
	a := marshal("b", 1)
	b := marshal("aa", 1)
	if codec.Compare(a, b) <= 0 {
		t.Fatal("expected 'b' > 'aa' lexicographically")
	}
}

func TestSize_MatchesMarshalLen(t *testing.T) {
	k, v := "hello", uint32(42)
	if codec.Size(k, v) != len(marshal(k, v)) {
		t.Fatal("Size should match the actual length of the marshaled record")
	}
}
