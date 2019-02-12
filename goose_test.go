package goose

import (
	"go/ast"
	"go/parser"
	"go/token"
	"strings"
	"testing"

	"github.com/tchajed/goose/coq"

	. "gopkg.in/check.v1"
)

func Test(t *testing.T) { TestingT(t) }

type ConversionSuite struct {
	fset *token.FileSet
	ctx  Ctx
}

func (s *ConversionSuite) SetUpTest(c *C) {
	s.fset = token.NewFileSet()
	s.ctx = NewCtx(s.fset, Config{})
}

// Convert loads Go source as a single, literal file and converts it to Gallina
func (s ConversionSuite) Convert(src string) []coq.Decl {
	srcCode := "package example\n\n" + strings.TrimSpace(src)
	f, err := parser.ParseFile(s.fset, "test.go",
		srcCode,
		parser.ParseComments)
	if err != nil {
		panic(err) // problem with test code
	}
	err = s.ctx.TypeCheck("example", []*ast.File{f})
	if err != nil {
		panic(err) // problem with test code
	}
	return s.ctx.FileDecls(f)

}

var _ = Suite(&ConversionSuite{})

func (s *ConversionSuite) TestEmpty(c *C) {
	decls := s.Convert(``)
	c.Assert(decls, HasLen, 0)
}

const filesysImport = `import "github.com/tchajed/goose/machine/filesys"`
const fsDecl = `var fs filesys.Filesys = filesys.Fs`
const fsPreamble = filesysImport + "\n\n" + fsDecl + "\n"

func (s *ConversionSuite) TestGlobalFilesys(c *C) {
	decls := s.Convert(fsPreamble)
	c.Assert(decls, HasLen, 0)
}

func (s *ConversionSuite) TestStructDecl(c *C) {
	decls := s.Convert(fsPreamble + `
// A Table provides fast access to an on-disk table
type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}`)
	c.Assert(decls, HasLen, 1)

	c.Check(decls[0], DeepEquals, coq.StructDecl{
		Name:    "Table",
		Comment: "A Table provides fast access to an on-disk table",
		Fields: []coq.FieldDecl{
			{"Index", coq.MapType{coq.TypeIdent("uint64")}},
			{"File", coq.TypeIdent("Fd")},
		},
	})
}

func callExpr(name string, args ...coq.Expr) coq.CallExpr {
	return coq.CallExpr{MethodName: name, Args: args}
}

func ident(name string) coq.IdentExpr {
	return coq.IdentExpr(name)
}

func field(name string, e coq.Expr) coq.FieldVal {
	return coq.FieldVal{name, e}
}

func binding(name string, e coq.Expr) coq.Binding {
	return coq.Binding{Name: name, Expr: e}
}

func (s *ConversionSuite) TestStraightLineFunc(c *C) {
	decls := s.Convert(fsPreamble + `
// A Table provides fast access to an on-disk table
type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}

// CreateTable creates a new, empty table.
func CreateTable(p string) Table {
	index := make(map[uint64]uint64)
	f := fs.Create(p)
	fs.Close(f)
	f2 := fs.Open(p)
	return Table{Index: index, File: f2}
}
`)
	c.Assert(decls, HasLen, 2)
	c.Check(decls[1], DeepEquals, coq.FuncDecl{
		Name: "CreateTable",
		Args: []coq.FieldDecl{
			{"p", coq.TypeIdent("Path")},
		},
		ReturnType: coq.StructName("Table"),
		Body: coq.BlockExpr{
			[]coq.Binding{
				binding("index", callExpr("Data.newHashTable", coq.TypeIdent("uint64"))),
				binding("f", callExpr("FS.create", ident("p"))),
				anon(callExpr("FS.close", ident("f"))),
				binding("f2", callExpr("FS.open", ident("p"))),
				anon(coq.ReturnExpr{coq.StructLiteral{
					"Table",
					[]coq.FieldVal{
						field("Index", ident("index")),
						field("File", ident("f2")),
					},
				}}),
			},
		},
		Comment: "CreateTable creates a new, empty table.",
	})
}
