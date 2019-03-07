package coq

import (
	"testing"

	. "gopkg.in/check.v1"
)

func Test(t *testing.T) { TestingT(t) }

type CoqSuite struct{}

var _ = Suite(&CoqSuite{})

func (s *CoqSuite) TestPp(c *C) {
	var pp buffer
	pp.Indent(2)
	pp.Add("%s", "")
	pp.Add("%s\n%s", "foo", "bar")
	pp.Block("call(", "%s)", "big\narg")
	pp.Indent(-len("call("))
	pp.AddComment("a multiline\ncomment")
	pp.Indent(-2)
	pp.AddLine("final line")
	c.Check(pp.Build(), Equals, `
  foo
  bar
  call(big
       arg)
  (* a multiline
     comment *)
final line`)
}
