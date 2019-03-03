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
			{"Value", SliceType{TypeIdent("byte")}},
		},
		Comment: "An Entry is a key-value pair.",
	}.CoqDecl(), Equals, strings.TrimSpace(`
Module Entry.
  (* An Entry is a key-value pair. *)
  Record t := mk {
    Key: uint64;
    Value: slice.t byte;
  }.
  Global Instance t_zero : HasGoZero t := mk (zeroValue _) (zeroValue _).
End Entry.`))
}

func (s *CoqSuite) TestTypes(c *C) {
	c.Check(MapType{TypeIdent("uint64")}.Coq(), Equals, "Map uint64")
	c.Check(StructName("Table").Coq(), Equals, "Table.t")
}

func callExpr(name string, args ...Expr) CallExpr {
	return CallExpr{MethodName: name, Args: args}
}

func binding(name string, e Expr) Binding {
	return Binding{Names: []string{name}, Expr: e}
}

func ident(name string) IdentExpr {
	return IdentExpr(name)
}

func (s *CoqSuite) TestStraightLineCode(c *C) {
	retVal := NewStructLiteral("Table")
	retVal.AddField("Index", IdentExpr("index"))
	retVal.AddField("File", IdentExpr("f2"))
	expr := BlockExpr{
		[]Binding{
			binding("index", callExpr("Data.newHashTable", TypeIdent("uint64"))),
			binding("f", callExpr("FS.create", IdentExpr("p"))),
			NewAnon(callExpr("FS.close", IdentExpr("f"))),
			binding("f2", callExpr("FS.open", IdentExpr("p"))),
			NewAnon(ReturnExpr{retVal}),
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

func (s *CoqSuite) TestFuncDecl(c *C) {
	body := BlockExpr{
		[]Binding{
			NewAnon(ReturnExpr{IdentExpr("0")}),
		},
	}
	f := FuncDecl{
		Name: "returnConstant",
		Args: []FieldDecl{
			{"p", TypeIdent("Path")},
			{"f", TypeIdent("Fd")},
		},
		ReturnType: TypeIdent("uint64"),
		Body:       body,
		Comment:    "returnConstant ignores its arguments",
	}
	c.Check(f.CoqDecl(), Equals, strings.TrimSpace(`
(* returnConstant ignores its arguments *)
Definition returnConstant (p:Path) (f:Fd) : proc uint64 :=
  Ret 0.
`))
}

func tupleExpr(es ...Expr) Expr {
	return NewTuple(es)
}

func tupleType(ts ...Type) Type {
	return NewTupleType(ts)
}

func block(exprs ...Binding) BlockExpr {
	return BlockExpr{Bindings: exprs}
}

func retBinding(e Expr) Binding {
	return NewAnon(ReturnExpr{Value: e})
}

func (s *CoqSuite) TestTuples(c *C) {
	c.Check(tupleExpr(IdentExpr("a")).Coq(), Equals, "a")
	c.Check(tupleExpr(IdentExpr("a"), IdentExpr("b")).Coq(),
		Equals, "(a, b)")
	c.Check(tupleType(TypeIdent("uint64"), MapType{TypeIdent("uint64")}).Coq(),
		Equals, "(uint64 * Map uint64)")

	entry := NewStructLiteral("Entry")
	entry.AddField("Key", IntLiteral{0})
	entry.AddField("Value", IdentExpr("_"))

	c.Check(tupleExpr(entry, IntLiteral{1}).Coq(),
		Equals, strings.TrimSpace(`
({| Entry.Key := 0;
    Entry.Value := _; |}, 1)`))
}

func (s *CoqSuite) TestBinOps(c *C) {
	x := IdentExpr("a")
	y := IntLiteral{1}
	c.Check(BinaryExpr{x, OpPlus, y}.Coq(),
		Equals, "a + 1")
	c.Check(BinaryExpr{x, OpEquals, y}.Coq(),
		Equals, "a == 1")
	c.Check(BinaryExpr{callExpr("slice.len", x), OpLessThan, y}.Coq(),
		Equals, "compare_to (slice.len a) 1 Lt")
}

func (s *CoqSuite) TestIntLiterals(c *C) {
	c.Check(IntLiteral{0}.Coq(), Equals, "0")
	c.Check(IntLiteral{1}.Coq(), Equals, "1")
	c.Check(IntLiteral{2}.Coq(), Equals, "2")
	c.Check(IntLiteral{4096}.Coq(), Equals, "4096")
}

func (s *CoqSuite) TestIfExpr(c *C) {
	lenP := callExpr("slice.len", IdentExpr("p"))
	ife := IfExpr{
		Cond: BinaryExpr{lenP, OpLessThan, IntLiteral{8}},
		Then: block(retBinding(tupleExpr(IntLiteral{0}, IntLiteral{0}))),
		Else: ReturnExpr{IdentExpr("tt")},
	}
	c.Check(ife.Coq(),
		Equals, strings.TrimSpace(`
if compare_to (slice.len p) 8 Lt
then Ret (0, 0)
else Ret tt
`))
}

func (s *CoqSuite) TestDestructuringBinding(c *C) {
	code := block(
		Binding{[]string{"x", "l"}, callExpr("Data.uint64Get", IdentExpr("p"))},
		retBinding(IdentExpr("x")),
	)
	c.Check(code.Coq(), Equals, strings.TrimSpace(`
let! (x, l) <- Data.uint64Get p;
Ret x
`))
}

func (s *CoqSuite) TestSliceType(c *C) {
	c.Check(SliceType{TypeIdent("byte")}.Coq(), Equals, "slice.t byte")
	c.Check(SliceType{StructName("Table")}.Coq(), Equals, "slice.t Table.t")
}

func (s *CoqSuite) TestPureImpure(c *C) {
	xyz := BinaryExpr{
		BinaryExpr{ident("x"), OpPlus, ident("y")},
		OpPlus, ident("z"),
	}
	c.Check(block(
		binding("x",
			PureCall(callExpr("slice.length", ident("p")))),
		binding("y",
			BinaryExpr{IntLiteral{2}, OpPlus, IntLiteral{3}}),
		binding("z",
			callExpr("Data.uint64Get", ident("p"))),
		retBinding(xyz),
	).Coq(), Equals, strings.TrimSpace(`
let x := slice.length p in
let y := 2 + 3 in
z <- Data.uint64Get p;
Ret (x + y + z)`))
}
