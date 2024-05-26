package newloop

import (
	"testing"
)

func TestAll(t *testing.T) {
	if sumBasic(5) != 15 {
		t.Fatal()
	}
	if sumBasicNew(5) != 15 {
		t.Fatal()
	}
	if sumIter(5) != 15 {
		t.Fatal()
	}
	if sumIterNew(5) != 15 {
		t.Fatal()
	}
}
