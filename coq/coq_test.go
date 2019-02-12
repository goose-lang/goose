package coq

import (
	"strings"
	"testing"

	. "gopkg.in/check.v1"
)

func Test(t *testing.T) { TestingT(t) }

type CoqSuite struct{}

var _ = Suite(&CoqSuite{})

func (s *CoqSuite) TestRecord(c *C) {
	c.Assert(StructDecl{
		Name: "Entry",
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

func callExpr(name string, args ...Expr) CallExpr {
	return CallExpr{MethodName: name, Args: args}
}

func field(name string, e Expr) FieldVal {
	return FieldVal{name, e}
}

func binding(name string, e Expr) Binding {
	return Binding{Name: name, Expr: e}
}

func anon(e Expr) Binding {
	return binding("", e)
}

func (s *CoqSuite) TestStraightLineCode(c *C) {
	expr := BlockExpr{
		[]Binding{
			binding("index", callExpr("Data.newHashTable", TypeIdent("uint64"))),
			binding("f", callExpr("FS.create", IdentExpr("p"))),
			anon(callExpr("FS.close", IdentExpr("f"))),
			binding("f2", callExpr("FS.open", IdentExpr("p"))),
			anon(ReturnExpr{StructLiteral{
				"Table",
				[]FieldVal{
					field("Index", IdentExpr("index")),
					field("File", IdentExpr("f2")),
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
