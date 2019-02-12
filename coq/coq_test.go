package coq

import (
	"go/ast"
	"go/parser"
	"go/token"
	"strings"
	"testing"

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
func (s ConversionSuite) Convert(src string) []Decl {
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

	c.Check(decls[0], DeepEquals, StructDecl{
		name:    "Table",
		Comment: "A Table provides fast access to an on-disk table",
		Fields: []FieldDecl{
			{"Index", MapType{TypeIdent("uint64")}},
			{"File", TypeIdent("Fd")},
		},
	})
}

func callExpr(name string, args ...Expr) CallExpr {
	return CallExpr{MethodName: name, Args: args}
}

func ident(name string) IdentExpr {
	return IdentExpr(name)
}

func field(name string, e Expr) FieldVal {
	return FieldVal{name, e}
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
	c.Check(decls[1], DeepEquals, FuncDecl{
		name: "CreateTable",
		Args: []FieldDecl{
			{"p", TypeIdent("Path")},
		},
		ReturnType: StructName("Table"),
		Body: BlockExpr{
			[]Binding{
				Binding{"index", callExpr("Data.newHashTable", TypeIdent("uint64"))},
				Binding{"f", callExpr("FS.create", ident("p"))},
				anon(callExpr("FS.close", ident("f"))),
				Binding{"f2", callExpr("FS.open", ident("p"))},
				anon(ReturnExpr{StructLiteral{
					"Table",
					[]FieldVal{
						field("Index", ident("index")),
						field("File", ident("f2")),
					},
				}}),
			},
		},
		Comment: "CreateTable creates a new, empty table.",
	})
}

type CoqSuite struct{}

var _ = Suite(&CoqSuite{})

func (s *CoqSuite) TestRecord(c *C) {
	c.Assert(StructDecl{
		name: "Entry",
		Fields: []FieldDecl{
			{"Key", TypeIdent("uint64")},
			{"Value", ByteSliceType{}},
		},
		Comment: "An Entry is a key-value pair.",
	}.CoqDecl(), Equals, strings.TrimSpace(`
Module Entry.
  (* An Entry is a key-value pair. *)
  Record t := mk {
    Key: uint64;
    Value: ByteSlice;
  }.
End Entry.`))
}

func (s *CoqSuite) TestTypes(c *C) {
	c.Check(MapType{TypeIdent("uint64")}.Coq(), Equals, "HashTable uint64")
	c.Check(StructName("Table").Coq(), Equals, "Table.t")
}

func (s *CoqSuite) TestStraightLineCode(c *C) {
	expr := BlockExpr{
		[]Binding{
			Binding{"index", callExpr("Data.newHashTable", TypeIdent("uint64"))},
			Binding{"f", callExpr("FS.create", ident("p"))},
			anon(callExpr("FS.close", ident("f"))),
			Binding{"f2", callExpr("FS.open", ident("p"))},
			anon(ReturnExpr{StructLiteral{
				"Table",
				[]FieldVal{
					field("Index", ident("index")),
					field("File", ident("f2")),
				},
			}}),
		},
	}
	c.Check(expr.Coq(), Equals, strings.TrimSpace(`
index <- Data.newHashTable uint64;
f <- FS.create p;
_ <- FS.close f;
f2 <- FS.open p;
Ret {| Table.Index := index;
       Table.File := f2; |}
`))
}
