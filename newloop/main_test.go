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
	if sumFancy(5) != 15 {
		t.Fatal()
	}
	if sumFancyNew(5) != 15 {
		t.Fatal()
	}
}
