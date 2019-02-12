package coq

import (
	"go/ast"
	"go/parser"
	"go/token"
	"testing"

	. "gopkg.in/check.v1"
)

func Test(t *testing.T) { TestingT(t) }

type CoqSuite struct {
	fset *token.FileSet
	ctx  Ctx
}

func (s *CoqSuite) SetUpTest(c *C) {
	s.fset = token.NewFileSet()
	s.ctx = NewCtx(s.fset, Config{})
}

// Convert loads Go source as a single, literal file and converts it to Gallina
func (s CoqSuite) Convert(src string) []Decl {
	f, err := parser.ParseFile(s.fset, "test.go", "package example\n\n"+src, parser.ParseComments)
	if err != nil {
		panic(err) // problem with test code
	}
	err = s.ctx.TypeCheck("example", []*ast.File{f})
	if err != nil {
		panic(err) // problem with test code
	}
	return s.ctx.FileDecls(f)

}

var _ = Suite(&CoqSuite{})

func (s *CoqSuite) TestEmpty(c *C) {
	decls := s.Convert(``)
	c.Assert(decls, HasLen, 0)
}

const filesysImport = `import "github.com/tchajed/goose/machine/filesys"`
const fsDecl = `var fs filesys.Filesys = filesys.Fs`
const fsPreamble = filesysImport + "\n\n" + fsDecl + "\n"

func (s *CoqSuite) TestGlobalFilesys(c *C) {
	decls := s.Convert(fsPreamble)
	c.Assert(decls, HasLen, 0)
}

func (s *CoqSuite) TestStructDecl(c *C) {
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

func (s *CoqSuite) TestStraightLineFunc(c *C) {
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
