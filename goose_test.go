package goose

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"strings"
	"testing"

	. "gopkg.in/check.v1"

	"github.com/tchajed/goose/coq"
)

func Test(t *testing.T) { TestingT(t) }

func fileDecls(src string) ([]coq.Decl, error) {
	fset := token.NewFileSet()
	ctx := NewCtx(fset, Config{})
	srcCode := "package example\n" + "//line <test.go>:1\n" + strings.TrimSpace(src)
	f, err := parser.ParseFile(fset, "test.go",
		srcCode,
		parser.ParseComments)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		fmt.Fprintln(os.Stderr, src)
		panic("test code does not parse")
	}
	err = ctx.TypeCheck("example", []*ast.File{f})
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		fmt.Fprintln(os.Stderr, src)
		panic("test code does not type check")
	}
	return ctx.Decls(f)
}

// goFunc load go src and returns the last declaration as a function
func goFunc(src string) coq.FuncDecl {
	decls, err := fileDecls(src)
	if err != nil {
		panic(err)
	}
	return decls[len(decls)-1].(coq.FuncDecl)
}

type ConversionSuite struct {
}

var _ = Suite(&ConversionSuite{})

func (s *ConversionSuite) TestEmpty(c *C) {
	decls, err := fileDecls(``)
	c.Assert(err, IsNil)
	c.Assert(decls, HasLen, 0)
}

const filesysImport = `import "github.com/tchajed/goose/machine/filesys"`
const fsDecl = `var fs filesys.Filesys = filesys.Fs`
const fsPreamble = filesysImport + "\n\n" + fsDecl + "\n"

func (s *ConversionSuite) TestGlobalFilesys(c *C) {
	decls, err := fileDecls(fsPreamble)
	c.Assert(err, IsNil)
	c.Assert(decls, HasLen, 0)
}

func (s *ConversionSuite) TestStructDecl(c *C) {
	decls, err := fileDecls(fsPreamble + `
// A Table provides fast access to an on-disk table
type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}`)
	c.Assert(err, IsNil)
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
	decl := goFunc(fsPreamble + `
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
	c.Check(decl, DeepEquals, coq.FuncDecl{
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
	decl := goFunc(`
func ReturnTwo(p []byte) (uint64, uint64) {
	return 0, 0
}

func ReturnTwoWrapper(data []byte) (uint64, uint64) {
	a, b := ReturnTwo(data)
	return a, b
}
`)
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
	decl := goFunc(`
import "github.com/tchajed/goose/machine"

func DecodeUInt64(p []byte) (uint64, uint64) {
	if len(p) < 8 {
		return 0, 0
	}
	n := machine.UInt64Get(p)
	return n, 8
}`)
	lenP := coq.PureCall(callExpr("slice.length", ident("p")))
	ife := coq.IfExpr{
		Cond: coq.BinaryExpr{lenP, coq.OpLessThan, intLiteral(8)},
		Then: block(retBinding(tuple(intLiteral(0), intLiteral(0)))),
		Else: block(
			coq.Binding{
				[]string{"n"},
				callExpr("Data.uint64Get", ident("p")),
			},
			retBinding(tuple(ident("n"), intLiteral(8)))),
	}
	c.Check(decl.Body, DeepEquals, block(coq.NewAnon(ife)))
}

func (s *ConversionSuite) TestEmptyFunc(c *C) {
	decl := goFunc(`func DoNothing(){}`)
	c.Check(decl.Body, DeepEquals,
		block(retBinding(ident("tt"))),
	)
}

func (s *ConversionSuite) TestStructNil(c *C) {
	decl := goFunc(`
type HasNil struct{
	Data []byte
}

func NewHasNil() HasNil {
    return HasNil{Data: nil}
}`)
	c.Check(decl.Body, DeepEquals,
		block(retBinding(coq.StructLiteral{
			StructName: "HasNil",
			Elts: []coq.FieldVal{
				{"Data", callExpr("slice.nil", coq.TypeIdent("_"))},
			},
		})))
}

func (s *ConversionSuite) TestSliceExpr(c *C) {
	decl := goFunc(`
func SliceExample(p []byte) ([]byte, []byte) {
	return p[:1], p[1:]
}`)
	c.Check(decl.Body, DeepEquals,
		block(retBinding(tuple(
			coq.PureCall(callExpr("slice.take", intLiteral(1), ident("p"))),
			coq.PureCall(callExpr("slice.skip", intLiteral(1), ident("p"))),
		))))
}

func (s *ConversionSuite) TestPureImpure(c *C) {
	decl := goFunc(`
import "github.com/tchajed/goose/machine"

func PureDemo(p []byte) uint64 {
  x := uint64(len(p))
  y := uint64(2 + 3)
  z := machine.UInt64Get(p)
  return x + y + z
}`)
	xyz := coq.BinaryExpr{
		coq.BinaryExpr{ident("x"), coq.OpPlus, ident("y")},
		coq.OpPlus, ident("z"),
	}
	c.Check(decl.Body, DeepEquals,
		block(
			binding("x",
				coq.PureCall(callExpr("slice.length", ident("p")))),
			binding("y",
				coq.BinaryExpr{intLiteral(2), coq.OpPlus, intLiteral(3)}),
			binding("z",
				callExpr("Data.uint64Get", ident("p"))),
			retBinding(xyz),
		),
	)
}
