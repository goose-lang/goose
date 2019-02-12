package coq

import (
	"go/ast"
	"go/parser"
	"go/token"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestGlobalFilesys(t *testing.T) {
	assert := assert.New(t)
	fset := token.NewFileSet()

	f, err := parser.ParseFile(fset, "test.go",
		`package example
import "github.com/tchajed/goose/machine/filesys"

var fs filesys.Filesys = filesys.Fs
`, parser.ParseComments)
	assert.NoError(err, "test code does not parse")

	ctx := NewCtx(fset, Config{})
	err = ctx.TypeCheck("example", []*ast.File{f})
	assert.NoError(err, "test code does not type check")

	decls := ctx.FileDecls(f)
	assert.Empty(decls)
}
