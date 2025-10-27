package chan_spec_raw_examples

import "testing"

func TestAll(t *testing.T) {
	TestHelloWorldSync()
	TestHelloWorldWithTimeout()
	TestDSPExample()
	TestFibConsumer()
	TestSelectNbNoPanic()
	TestSelectReadyCaseNoPanic()
}

func TestAllX(t *testing.T) {
	TestHelloWorldSyncX()
	TestHelloWorldWithTimeoutX()
	TestDSPExampleX()
	TestFibConsumerX()
	TestSelectNbNoPanicX()
	TestSelectReadyCaseNoPanicX()
}
