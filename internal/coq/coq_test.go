package coq

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestPp(t *testing.T) {
	assert := assert.New(t)
	var pp buffer
	pp.Indent(2)
	pp.Add("%s", "")
	pp.Add("%s\n%s", "foo", "bar")
	pp.Block("call(", "%s)", "big\narg")
	pp.Indent(-len("call("))
	pp.AddComment("a multiline\ncomment")
	pp.Indent(-2)
	pp.AddLine("final line")
	assert.Equal(`
  foo
  bar
  call(big
       arg)
  (* a multiline
     comment *)
final line`, pp.Build())
}
