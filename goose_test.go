package goose

import (
	"go/ast"
	"go/parser"
	"go/token"
	"strings"
	"testing"

	. "gopkg.in/check.v1"

	"github.com/tchajed/goose/coq"
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
	return coq.FieldVal{Field: name, Value: e}
}

func binding(name string, e coq.Expr) coq.Binding {
	return coq.Binding{Names: []string{name}, Expr: e}
}

func block(exprs ...coq.Binding) coq.BlockExpr {
	return coq.BlockExpr{Bindings: exprs}
}

func retBinding(e coq.Expr) coq.Binding {
	return coq.NewAnon(coq.ReturnExpr{Value: e})
}

func tuple(es ...coq.Expr) coq.Expr {
	return coq.NewTuple(es)
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
		Body: block(
			binding("index", callExpr("Data.newHashTable", coq.TypeIdent("uint64"))),
			binding("f", callExpr("FS.create", ident("p"))),
			coq.NewAnon(callExpr("FS.close", ident("f"))),
			binding("f2", callExpr("FS.open", ident("p"))),
			retBinding(coq.StructLiteral{
				StructName: "Table",
				Elts: []coq.FieldVal{
					field("Index", ident("index")),
					field("File", ident("f2")),
				},
			}),
		),
		Comment: "CreateTable creates a new, empty table.",
	})
}

func (s *ConversionSuite) TestMultipleReturn(c *C) {
	decls := s.Convert(`
func ReturnTwo(p []byte) (uint64, uint64) {
	return 0, 0
}

func ReturnTwoWrapper(data []byte) (uint64, uint64) {
	a, b := ReturnTwo(data)
	return a, b
}
`)
	decl := decls[1].(coq.FuncDecl)
	c.Assert(decl.Name, Equals, "ReturnTwoWrapper",
		Commentf("declarations returned out-of-order"))

	c.Check(decl.Body, DeepEquals, block(
		coq.Binding{[]string{"a", "b"},
			callExpr("ReturnTwo", ident("data"))},
		retBinding(tuple(ident("a"), ident("b"))),
	))
}

func intLiteral(x uint64) coq.IntLiteral {
	return coq.IntLiteral{Value: x}
}

func (s *ConversionSuite) TestIfStmt(c *C) {
	decls := s.Convert(`
import "github.com/tchajed/goose/machine"

func DecodeUInt64(p []byte) (uint64, uint64) {
	if len(p) < 8 {
		return 0, 0
	}
	n := machine.UInt64Get(p)
	return n, 8
}`)
	decl := decls[0].(coq.FuncDecl)
	c.Assert(decl.Name, Equals, "DecodeUInt64")

	lenP := callExpr("slice.length", ident("p"))
	ife := coq.IfExpr{
		Cond: coq.BinaryExpr{lenP, coq.OpLessThan, intLiteral(8)},
		Then: block(retBinding(tuple(intLiteral(0), intLiteral(0)))),
		Else: coq.ReturnExpr{ident("tt")},
	}
	// TODO: this is actually the wrong code for the example;
	//   code following an early return needs to be lifted to the else of the if statement.
	c.Check(decl.Body, DeepEquals, coq.BlockExpr{
		Bindings: []coq.Binding{
			coq.NewAnon(ife),
			{[]string{"n"},
				callExpr("Data.uint64Get", ident("p"))},
			retBinding(tuple(ident("n"), intLiteral(8))),
		},
	})
}

func (s *ConversionSuite) TestEmptyFunc(c *C) {
	decls := s.Convert(`func DoNothing(){}`)
	decl := decls[0].(coq.FuncDecl)
	c.Check(decl.Body, DeepEquals,
		block(retBinding(ident("tt"))),
	)
}
