package unittest

import (
	"testing"

	. "gopkg.in/check.v1"
)

// TODO: separate GooseLang semantics tests from simpler syntactic unit tests
// TODO: autogenerate this file

func Test(t *testing.T) { TestingT(t) }

type TestSuite struct{}

var _ = Suite(&TestSuite{})

func (suite *TestSuite) TestEncDec32Simple(c *C) {
	c.Check(testEncDec32Simple(), Equals, true)
}

func (suite *TestSuite) TestEncDec32S(c *C) {
	c.Check(testEncDec32(), Equals, true)
}

func (suite *TestSuite) TestEncDec64Simple(c *C) {
	c.Check(testEncDec64Simple(), Equals, true)
}

func (suite *TestSuite) TestEncDec64(c *C) {
	c.Check(testEncDec64(), Equals, true)
}

func (suite *TestSuite) TestReverseAssignOps32(c *C) {
	c.Check(testReverseAssignOps32(), Equals, true)
}

func (suite *TestSuite) TestReverseAssignOps64(c *C) {
	c.Check(testReverseAssignOps64(), Equals, true)
}

func (suite *TestSuite) TestAdd64Equals(c *C) {
	c.Check(testAdd64Equals(), Equals, true)
}

func (suite *TestSuite) TestMinus64Equals(c *C) {
	c.Check(testMinus64Equals(), Equals, true)
}

func (suite *TestSuite) TestShortcircuitAndTF(c *C) {
	c.Check(testShortcircuitAndTF(), Equals, true)
}

func (suite *TestSuite) TestShortcircuitAndFT(c *C) {
	c.Check(testShortcircuitAndFT(), Equals, true)
}

func (suite *TestSuite) TestShortcircuitOrTF(c *C) {
	c.Check(testShortcircuitOrTF(), Equals, true)
}

func (suite *TestSuite) TestShortcircuitOrFT(c *C) {
	c.Check(testShortcircuitOrFT(), Equals, true)
}

func (suite *TestSuite) TestOverwriteArray(c *C) {
	c.Check(testOverwriteArray(), Equals, true)
}

func (suite *TestSuite) TestFunctionOrdering(c *C) {
	c.Check(testFunctionOrdering(), Equals, true)
}

func (suite *TestSuite) TestStandardForLoop(c *C) {
	c.Check(testStandardForLoop(), Equals, true)
}

func (suite *TestSuite) TestConditionalAssign(c *C) {
	c.Check(testConditionalAssign(), Equals, true)
}

func (suite *TestSuite) TestConversions(c *C) {
	c.Check(testConversions(), Equals, true)
}
