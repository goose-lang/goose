package chan_spec_raw_examples

import (
	"strings"
	"testing"
)

func TestAll(t *testing.T) {
	TestHelloWorldSync()
	TestHelloWorldWithTimeout()
	TestDSPExample()
	TestFibConsumer()
	TestSelectNbNoPanic()
	TestSelectReadyCaseNoPanic()
}

func TestHigherOrderExample(t *testing.T) {
	responses := HigherOrderExample()
	expected := []string{"hello world", "HELLO", "world"}
	if !strings.EqualFold(strings.Join(responses, ""), strings.Join(expected, "")) {
		t.Errorf("Expected %v, got %v", expected, responses)
	}
}
