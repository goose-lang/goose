package glang

import (
	"fmt"
	"io"
	"math/big"
	"path"
	"path/filepath"
	"sort"
	"strings"
)

func addParens(needs_paren bool, expr string) string {
	if needs_paren {
		return "(" + expr + ")"
	} else {
		return expr
	}
}

// buffer is a simple indenting pretty printer
type buffer struct {
	lines       []string
	indentLevel int
}

func (pp buffer) indentation() string {
	b := make([]byte, pp.indentLevel)
	for i := range b {
		b[i] = ' '
	}
	return string(b)
}

func (pp *buffer) appendLine(line string) {
	pp.lines = append(pp.lines, line)
}

func (pp *buffer) AddLine(line string) {
	if line == "" {
		pp.appendLine("")
	} else {
		pp.appendLine(pp.indentation() + indent(pp.indentLevel, line))
	}
}

// Add adds formatted to the buffer
func (pp *buffer) Add(format string, args ...interface{}) {
	pp.AddLine(fmt.Sprintf(format, args...))
}

func (pp *buffer) Indent(spaces int) {
	pp.indentLevel += spaces
}

func (pp *buffer) Block(prefix string, format string, args ...interface{}) int {
	pp.AddLine(prefix + indent(len(prefix), fmt.Sprintf(format, args...)))
	pp.Indent(len(prefix))
	return len(prefix)
}

func (pp buffer) Build() string {
	return strings.Join(pp.lines, "\n")
}

func indent(spaces int, s string) string {
	lines := strings.Split(s, "\n")
	indentation := strings.Repeat(" ", spaces)
	for i, line := range lines {
		if i == 0 || line == "" {
			continue
		}
		lines[i] = indentation + line
	}
	return strings.Join(lines, "\n")
}

func (pp *buffer) AddComment(c string) {
	if c == "" {
		return
	}
	// these hacks ensure that Go comments don't insert stray Coq comments
	c = strings.ReplaceAll(c, "(*", "( *")
	c = strings.ReplaceAll(c, "*)", "* )")
	indent := pp.Block("(* ", "%s *)", c)
	pp.Indent(-indent)
}

func quote(s string) string {
	return `"` + s + `"`
}

// FIXME: why is this needed?
func binder(s string) string {
	if s == "_" {
		return "<>"
	}
	return quote(s)
}

// FieldDecl is a name:type declaration (for a struct or function binders)
type FieldDecl struct {
	Name string
	Type Type
}

func (d FieldDecl) CoqBinder() string {
	return binder(d.Name)
}

func (d FieldDecl) Coq(needs_paren bool) string {
	return binder(d.Name)
}

// StructDecl is a Coq record for a Go struct
type StructType struct {
	Fields []FieldDecl
}

// CoqDecl implements the Decl interface
//
// A struct declaration simply consists of the struct descriptor
func (d StructType) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("structT [")
	pp.Indent(2)
	for i, fd := range d.Fields {
		sep := ";"
		if i == len(d.Fields)-1 {
			sep = ""
		}
		pp.Add("%s :: %s%s", quote(fd.Name), fd.Type.Coq(false), sep)
	}
	pp.Indent(-2)
	pp.AddLine("]")
	return addParens(needs_paren, pp.Build())
}

type TypeDecl struct {
	Name       string
	Body       Type
	TypeParams []TypeIdent
}

func (d TypeDecl) CoqDecl() string {
	var pp buffer

	typeParams := ""
	for _, t := range d.TypeParams {
		typeParams += fmt.Sprintf("(%s: go_type) ", t.Coq(false))
	}

	pp.Add("Definition %s %s: go_type := %s.", d.Name, typeParams, d.Body.Coq(false))
	return pp.Build()
}

func (d TypeDecl) DefName() (bool, string) {
	return true, d.Name
}

// Type represents some Coq type.
//
// Structurally identical to Expr but serves as a nice annotation in the type
// system for where types are expected.
type Type interface {
	// If needs_paren is true, this should be generated with parentheses.
	Coq(needs_paren bool) string
}

// TypeIdent is an identifier referencing a type.
//
// Much like the Type interface this is the same as Ident but signals that a Go
// type rather than a value is being referenced.
type TypeIdent string

func (t TypeIdent) Coq(needs_paren bool) string {
	return string(t)
}

type MapType struct {
	Key   Type
	Value Type
}

func (t MapType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaIdent("mapT"), t.Key, t.Value).Coq(needs_paren)
}

type ChanType struct {
	Elem Type
}

func (t ChanType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaIdent("chanT"), t.Elem).Coq(needs_paren)
}

type FuncType struct {
}

func (t FuncType) Coq(needs_paren bool) string {
	return "funcT"
}

type SliceType struct {
	Value Type
}

func (t SliceType) Coq(needs_paren bool) string {
	return "sliceT"
}

type ArrayType struct {
	Len  uint64
	Elem Type
}

func (t ArrayType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaIdent(fmt.Sprintf("arrayT %d", t.Len)), t.Elem).Coq(needs_paren)
}

type Expr interface {
	// If needs_paren is true, this should be generated with parentheses.
	Coq(needs_paren bool) string
}

// GallinaIdent is a identifier in Gallina (and not a variable)
//
// A GallinaIdent is translated literally to Coq.
type GallinaIdent string

func (e GallinaIdent) Coq(needs_paren bool) string {
	return string(e)
}

// A Go qualified identifier, which is translated to a Gallina qualified
// identifier.
type PackageIdent struct {
	Package string
	Ident   string
}

func (e PackageIdent) Coq(needs_paren bool) string {
	return fmt.Sprintf("%s.%s", ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(e.Package), e.Ident)
}

var Skip Expr = GallinaIdent("Skip")

type ParenExpr struct {
	Inner Expr
}

func (e ParenExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("(%s)", e.Inner.Coq(needs_paren))
}

// IdentExpr is a go_lang-level variable
//
// An IdentExpr is quoted in Coq.
type IdentExpr string

func (e IdentExpr) Coq(needs_paren bool) string {
	return quote(string(e))
}

// GallinaString is a Gallina string, wrapped in quotes
//
// This is functionally identical to IdentExpr, but semantically quite
// different.
type GallinaString string

func (s GallinaString) Coq(needs_paren bool) string {
	return quote(string(s))
}

// CallExpr includes primitives and references to other functions.
type CallExpr struct {
	MethodName Expr
	Args       []Expr
}

// NewCallExpr is a convenience to construct a CallExpr statically, especially
// for a fixed number of arguments.
func NewCallExpr(name Expr, args ...Expr) CallExpr {
	if len(args) == 0 {
		args = []Expr{Tt}
	}
	return CallExpr{MethodName: name, Args: args}
}

func (s CallExpr) Coq(needs_paren bool) string {
	comps := []string{s.MethodName.Coq(true)}

	for _, a := range s.Args {
		comps = append(comps, a.Coq(true))
	}
	return addParens(needs_paren, strings.Join(comps, " "))
}

type ContinueExpr struct {
}

func (e ContinueExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("continue: #()")
}

type BreakExpr struct {
}

func (e BreakExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("break: #()")
}

type ReturnExpr struct {
	Value Expr
}

func (e ReturnExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("return: %s", e.Value.Coq(needs_paren))
}

type DoExpr struct {
	Expr Expr
}

func (b DoExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("do:  %s", b.Expr.Coq(true))
	return addParens(needs_paren, pp.Build())
}

func NewDoSeq(e, cont Expr) SeqExpr {
	return SeqExpr{Expr: DoExpr{Expr: e}, Cont: cont}
}

type SeqExpr struct {
	Expr, Cont Expr
}

func (b SeqExpr) Coq(needs_paren bool) string {
	var pp buffer

	if b.Cont == nil {
		pp.Add("%s", b.Expr.Coq(false))
		return addParens(needs_paren, pp.Build())
	}

	pp.Add("%s;;;", b.Expr.Coq(false))
	pp.Add("%s", b.Cont.Coq(false))
	return addParens(needs_paren, pp.Build())
}

type LetExpr struct {
	// Names is a list to support anonymous and tuple-destructuring bindings.
	//
	// If Names is an empty list the binding is anonymous.
	Names   []string
	ValExpr Expr
	Cont    Expr
}

func (e LetExpr) isAnonymous() bool {
	return len(e.Names) == 0
}

func (b LetExpr) Coq(needs_paren bool) string {
	var pp buffer
	if b.Cont == nil {
		if !b.isAnonymous() {
			panic("let expr with nil cont but non-anonymous binding")
		}
		pp.Add("%s", b.ValExpr.Coq(false))
		return addParens(needs_paren, pp.Build())
	}

	if b.isAnonymous() {
		pp.Add("%s;;", b.ValExpr.Coq(false))
	} else if len(b.Names) == 1 {
		pp.Add("let: %s := %s in", binder(b.Names[0]), b.ValExpr.Coq(true))
	} else if len(b.Names) == 2 {
		pp.Add("let: (%s, %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			b.ValExpr.Coq(true))
	} else if len(b.Names) == 3 {
		pp.Add("let: ((%s, %s), %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			binder(b.Names[2]),
			b.ValExpr.Coq(true))
	} else if len(b.Names) == 4 {
		pp.Add("let: (((%s, %s), %s), %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			binder(b.Names[2]),
			binder(b.Names[3]),
			b.ValExpr.Coq(true))
	} else if len(b.Names) == 5 {
		pp.Add("let: ((((%s, %s), %s), %s), %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			binder(b.Names[2]),
			binder(b.Names[3]),
			binder(b.Names[4]),
			b.ValExpr.Coq(true))
	} else {
		panic(fmt.Sprintf("no support for destructuring more than %d return values (up to 5 supported)", len(b.Names)))
	}
	pp.Add("%s", b.Cont.Coq(false))
	return addParens(needs_paren, pp.Build())
}

type fieldVal struct {
	Field string
	Value Expr
}

// A StructLiteral represents a record literal construction using name fields.
//
// Relies on Coq record syntax to correctly order fields for the record's
// constructor.
type StructLiteral struct {
	StructType Expr
	Elts       []fieldVal
}

// AddField appends a new (field, val) pair to a StructLiteral.
func (sl *StructLiteral) AddField(field string, value Expr) {
	sl.Elts = append(sl.Elts, fieldVal{field, value})
}

func (sl StructLiteral) Coq(needs_paren bool) string {
	var pp buffer
	method := "struct.make"
	pp.Add("%s %s [{", method, sl.StructType.Coq(true))
	pp.Indent(2)
	for i, f := range sl.Elts {
		terminator := ";"
		if i == len(sl.Elts)-1 {
			terminator = ""
		}
		pp.Add("%s ::= %s%s", quote(f.Field), f.Value.Coq(false), terminator)
	}
	pp.Indent(-2)
	pp.Add("}]")
	return addParens(needs_paren, pp.Build())
}

type BoolLiteral bool

func (b BoolLiteral) Coq(needs_paren bool) string {
	if b {
		return "#true"
	} else {
		return "#false"
	}
}

var (
	False BoolLiteral = BoolLiteral(false)
	True  BoolLiteral = BoolLiteral(true)
)

type BoolVal struct {
	Value Expr
}

func (b BoolVal) Coq(needs_paren bool) string {
	return fmt.Sprintf("#%s", b.Value.Coq(true))
}

type UnitLiteral struct{}

var Tt UnitLiteral = struct{}{}

func (tt UnitLiteral) Coq(needs_paren bool) string {
	return "#()"
}

type ZLiteral struct {
	Value *big.Int
}

func (z ZLiteral) Coq(needs_paren bool) string {
	return z.Value.String()
}

type StringLiteral struct {
	Value string
}

func (s StringLiteral) Coq(needs_paren bool) string {
	return fmt.Sprintf(`"%s"`, strings.Replace(s.Value, `"`, `""`, -1))
}

type Int64Val struct {
	Value Expr
}

func (l Int64Val) Coq(needs_paren bool) string {
	return fmt.Sprintf("#(W64 %s)", l.Value.Coq(true))
}

type Int32Val struct {
	Value Expr
}

func (l Int32Val) Coq(needs_paren bool) string {
	return fmt.Sprintf("#(W32 %s)", l.Value.Coq(true))
}

type Int8Val struct {
	Value Expr
}

func (l Int8Val) Coq(needs_paren bool) string {
	return fmt.Sprintf("#(W8 %s)", l.Value.Coq(true))
}

type StringVal struct {
	Value Expr
}

func (l StringVal) Coq(needs_paren bool) string {
	return fmt.Sprintf(`#%s`, l.Value.Coq(true))
}

// BinOp is an enum for a Coq binary operator
type BinOp int

// Constants for the supported Coq binary operators
const (
	OpPlus BinOp = iota
	OpMinus
	OpEquals
	OpNotEquals
	OpLessThan
	OpGreaterThan
	OpLessEq
	OpGreaterEq

	OpEqualsZ
	OpLessThanZ
	OpGreaterThanZ
	OpLessEqZ
	OpGreaterEqZ

	OpGallinaAppend

	OpAppend
	OpMul
	OpQuot
	OpRem
	OpAnd
	OpOr
	OpXor
	OpLAnd
	OpLOr
	OpShl
	OpShr
)

type BinaryExpr struct {
	X  Expr
	Op BinOp
	Y  Expr
}

func (be BinaryExpr) Coq(needs_paren bool) string {
	coqBinOp := map[BinOp]string{
		OpPlus:          "+",
		OpMinus:         "-",
		OpEquals:        "=",
		OpNotEquals:     "≠",
		OpGallinaAppend: "++",
		OpAppend:        "+",
		OpMul:           "*",
		OpQuot:          "`quot`",
		OpRem:           "`rem`",
		OpLessThan:      "<",
		OpGreaterThan:   ">",
		OpLessEq:        "≤",
		OpGreaterEq:     "≥",

		OpEqualsZ:      "=?",
		OpLessThanZ:    "<?",
		OpGreaterThanZ: ">?",
		OpLessEqZ:      "<=?",
		OpGreaterEqZ:   ">=?",

		OpAnd:  "`and`",
		OpOr:   "`or`",
		OpXor:  "`xor`",
		OpLAnd: "&&",
		OpLOr:  "||",
		OpShl:  "≪",
		OpShr:  "≫",
	}
	if binop, ok := coqBinOp[be.Op]; ok {
		expr := fmt.Sprintf("%s %s %s",
			be.X.Coq(true), binop, be.Y.Coq(true))
		return addParens(needs_paren, expr)
	}

	panic(fmt.Sprintf("unknown binop %d", be.Op))
}

type GallinaNotExpr struct {
	X Expr
}

func (e GallinaNotExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("(negb %s)", e.X.Coq(true))
}

type NotExpr struct {
	X Expr
}

func (e NotExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("(~ %s)", e.X.Coq(true))
}

type TupleExpr []Expr

func (te TupleExpr) Coq(needs_paren bool) string {
	var comps []string
	for _, t := range te {
		comps = append(comps, t.Coq(false))
	}
	return fmt.Sprintf("(%s)",
		indent(1, strings.Join(comps, ", ")))
}

type ListExpr []Expr

func (le ListExpr) Coq(needs_paren bool) string {
	var comps []string
	for _, t := range le {
		comps = append(comps, t.Coq(false))
	}
	elements := indent(1, strings.Join(comps, "; "))
	if strings.HasPrefix(elements, "#") {
		// [# ...] is a vector notation while we want the list notation [ ... ]
		// (and `[#` is a single token even if the vector notation isn't in
		// scope)
		return fmt.Sprintf("[ %s ]", elements)
	}
	return fmt.Sprintf("[%s]", elements)
}

type DerefExpr struct {
	X  Expr
	Ty Expr
}

func (e DerefExpr) Coq(needs_paren bool) string {
	expr := fmt.Sprintf("![%s] %s", e.Ty.Coq(false), e.X.Coq(true))
	return addParens(needs_paren, expr)
}

type RefExpr struct {
	X  Expr
	Ty Expr
}

func (e RefExpr) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaIdent("ref_ty"), e.Ty, e.X).Coq(needs_paren)
}

type StoreStmt struct {
	Dst Expr
	Ty  Expr
	X   Expr
}

func (e StoreStmt) Coq(needs_paren bool) string {
	expr := fmt.Sprintf("%s <-[%s] %s", e.Dst.Coq(true), e.Ty.Coq(false), e.X.Coq(true))
	return addParens(needs_paren, expr)
}

type IfExpr struct {
	Cond Expr
	Then Expr
	Else Expr
}

func flowBranch(pp *buffer, prefix string, e Expr, suffix string) {
	code := e.Coq(false) + suffix
	if !strings.ContainsRune(code, '\n') {
		// compact, single-line form
		indent := pp.Block(prefix+" ", "%s", code)
		pp.Indent(-indent)
		return
	}
	// full multiline, nicely indented form
	pp.AddLine(prefix)
	pp.Indent(2)
	pp.AddLine(code)
	pp.Indent(-2)
}

func (ife IfExpr) Coq(needs_paren bool) string {
	var pp buffer
	// Since we are parenthesesizing all if, we don't need to parenthesize the things inside the if
	pp.Add("(if: %s", ife.Cond.Coq(false))
	flowBranch(&pp, "then", ife.Then, "")
	flowBranch(&pp, "else", ife.Else, ")")
	return pp.Build()
}

// The init statement must wrap the ForLoopExpr, so it can make use of bindings
// introduced there.
type ForLoopExpr struct {
	Cond Expr
	Post Expr
	// the body of the loop
	Body Expr
}

func (e ForLoopExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("(for: (λ: <>, %s); (λ: <>, %s) := λ: <>,", e.Cond.Coq(false), e.Post.Coq(false))
	pp.Indent(2)
	pp.Add("%s)", e.Body.Coq(false))
	return pp.Build()
}

type ForRangeSliceExpr struct {
	Key   Binder
	Val   Binder
	Ty    Expr
	Slice Expr
	Body  Expr
}

func (e ForRangeSliceExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("slice.for_range %s %s (λ: %s %s,",
		e.Ty.Coq(true),
		e.Slice.Coq(true),
		binderToCoq(e.Key), binderToCoq(e.Val),
	)
	pp.Indent(2)
	if e.Key != nil && *e.Key != "_" {
		pp.Add("let: %s := ref_ty uint64T %s in", binderToCoq(e.Key), binderToCoq(e.Key))
	}
	if e.Val != nil && *e.Val != "_" {
		pp.Add("let: %s := ref_ty %s %s in", binderToCoq(e.Val), e.Ty.Coq(true), binderToCoq(e.Val))
	}
	pp.Add("%s)", e.Body.Coq(false))
	pp.Indent(-2)
	return addParens(needs_paren, pp.Build())
}

type Binder *IdentExpr

func binderToCoq(b Binder) string {
	if b == nil {
		return "<>"
	}
	return binder(string(*b))
}

// ForRangeMapExpr is a call to the map iteration helper.
type ForRangeMapExpr struct {
	// name of key and value identifiers
	KeyIdent, ValueIdent string
	// map to iterate over
	Map Expr
	// body of loop, with KeyIdent and ValueIdent as free variables
	Body Expr
}

func (e ForRangeMapExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("map.for_range %s (λ: %s %s,",
		e.Map.Coq(true),
		binder(e.KeyIdent), binder(e.ValueIdent))
	pp.Indent(2)
	pp.Add("%s)", e.Body.Coq(false))
	return addParens(needs_paren, pp.Build())
}

// SpawnExpr is a call to Spawn a thread running a procedure.
//
// The body can capture variables in the environment.
type SpawnExpr struct {
	Body Expr
}

func (e SpawnExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Block("Fork (", "%s)", e.Body.Coq(false))
	return addParens(needs_paren, pp.Build())
}

// FuncLit is an unnamed function literal, consisting of its parameters and body.
type FuncLit struct {
	Args []FieldDecl
	Body Expr
}

func (e FuncLit) Coq(needs_paren bool) string {
	var pp buffer

	var args []string
	for _, a := range e.Args {
		args = append(args, a.CoqBinder())
	}
	if len(args) == 0 {
		args = []string{"<>"}
	}
	sig := strings.Join(args, " ")

	pp.Add("(λ: %s,", sig)
	pp.Indent(2)
	defer pp.Indent(-2)
	pp.AddLine(e.Body.Coq(false))
	pp.Add(")")

	return pp.Build()
}

// FuncDecl declares a function, including its parameters and body.
type FuncDecl struct {
	Name       string
	TypeParams []TypeIdent
	RecvArg    *FieldDecl
	Args       []FieldDecl
	ReturnType Type
	Body       Expr
	Comment    string
}

// Signature renders the function declaration's bindings
func (d FuncDecl) Signature() string {
	var args []string
	if d.RecvArg != nil {
		args = append(args, d.RecvArg.CoqBinder())
	}
	for _, a := range d.Args {
		args = append(args, a.CoqBinder())
	}
	if len(d.Args) == 0 {
		args = append(args, "<>")
	}
	return strings.Join(args, " ")
}

// CoqDecl implements the Decl interface
//
// For FuncDecl this emits the Coq vernacular Definition that defines the whole
// function.
func (d FuncDecl) CoqDecl() string {
	var pp buffer
	pp.AddComment(d.Comment)

	typeParams := ""
	for _, t := range d.TypeParams {
		typeParams += fmt.Sprintf("(%s: go_type) ", t.Coq(false))
	}

	pp.Add("Definition %s %s: val :=", d.Name, typeParams)
	func() {
		pp.Indent(2)
		defer pp.Indent(-2)
		pp.Add("rec: \"%s\" %s :=", d.Name, d.Signature())
		pp.Indent(2)
		defer pp.Indent(-2)
		pp.AddLine(d.Body.Coq(false) + ".")
	}()
	return pp.Build()
}

func (d FuncDecl) DefName() (bool, string) {
	return true, d.Name
}

// CommentDecl is a top-level comment
//
// Pretends to be a declaration so it can sit among declarations within a file.
type CommentDecl string

// NewComment creates a CommentDecl with proper whitespacing.
func NewComment(s string) CommentDecl {
	comment := strings.TrimRight(s, " \t\n")
	return CommentDecl(comment)
}

// CoqDecl implements the Decl interface
//
// For CommentDecl this emits a Coq top-level comment.
func (d CommentDecl) CoqDecl() string {
	var pp buffer
	pp.AddComment(string(d))
	return pp.Build()
}

func (d CommentDecl) DefName() (bool, string) {
	return false, ""
}

type ConstDecl struct {
	Name    string
	Val     Expr
	Type    Expr
	Comment string
}

func (d ConstDecl) CoqDecl() string {
	var pp buffer
	pp.AddComment(d.Comment)
	indent := pp.Block("Definition ", "%s : %s := %s.",
		d.Name, d.Type.Coq(false), d.Val.Coq(false))
	pp.Indent(-indent)
	return pp.Build()
}

func (d ConstDecl) DefName() (bool, string) {
	return true, d.Name
}

type MethodSetDecl struct {
	DeclName    string
	MethodNames []string
	Methods     []Expr
}

func (d MethodSetDecl) CoqDecl() string {
	var pp buffer
	pp.Add("Definition %s : list (string * val) := [", d.DeclName)
	pp.Indent(2)
	for i, name := range d.MethodNames {
		sep := ";"
		if i == len(d.Methods)-1 {
			sep = ""
		}
		pp.Add("(\"%s\", %s%%V)%s", name, d.Methods[i].Coq(false), sep)
	}
	pp.Indent(-2)
	pp.Add("].")
	return pp.Build()
}

func (d MethodSetDecl) DefName() (bool, string) {
	return true, d.DeclName
}

type VarDecl struct {
	DeclName    string
	VarUniqueId Expr
}

func (d VarDecl) CoqDecl() string {
	return fmt.Sprintf("Definition %s : (string * string) := %s.", d.DeclName, d.VarUniqueId.Coq(false))
}

func (d VarDecl) DefName() (bool, string) {
	return true, d.DeclName
}

// Decl is a FuncDecl, StructDecl, CommentDecl, or ConstDecl
type Decl interface {
	CoqDecl() string
	DefName() (bool, string) // If true, then the Gallina identifier that is defined by this decl.
}

type TupleType []Type

// NewTupleType is a smart constructor that wraps multiple types in a TupleType
func NewTupleType(types []Type) Type {
	if len(types) == 1 {
		return types[0]
	}
	return TupleType(types)
}

func (tt TupleType) Coq(needs_paren bool) string {
	var comps []string
	for _, t := range tt {
		comps = append(comps, t.Coq(true))
	}
	return fmt.Sprintf("(%s)", strings.Join(comps, " * "))
}

type PtrType struct {
}

func (t PtrType) Coq(needs_paren bool) string {
	return "ptrT"
}

func TypeMethod(typeName string, methodName string) string {
	return fmt.Sprintf("%s__%s", typeName, methodName)
}

const importHeader string = `
From New.golang Require Import defn.
`

// These will not end up in `File.Decls`, they are put into `File.Imports` by `translatePackage`.
type ImportDecl struct {
	Path string
}

// This is an injective mapping
// FIXME: should really use this
func goPathToCoqPath(p string) string {
	p = strings.ReplaceAll(p, "_", "__")
	p = strings.ReplaceAll(p, ".", "_dot_")
	p = strings.ReplaceAll(p, "-", "_dash_")
	return p
}

func ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(p string) string {
	p = strings.ReplaceAll(p, "_", "_")
	p = strings.ReplaceAll(p, ".", "_")
	p = strings.ReplaceAll(p, "-", "_")
	return p
}

// ImportToPath converts a Go import path to a Coq path
//
// TODO: we basically don't handle the package name (determined by the package
//
//	statement in Go) differing from the basename of its parent directory
func ImportToPath(pkgPath, pkgName string) string {
	coqPath := ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkgPath)
	p := path.Dir(coqPath)
	filename := path.Base(coqPath) + ".v"
	return filepath.Join(p, filename)
}

func (decl ImportDecl) CoqDecl() string {
	coqImportQualid := strings.ReplaceAll(ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(decl.Path), "/", ".")
	return fmt.Sprintf("From New.code Require %s.", coqImportQualid)
}

func (decl ImportDecl) DefName() (bool, string) {
	return false, ""
}

// ImportDecls groups imports into one declaration so they can be printed
// without intervening blank spaces.
type ImportDecls []ImportDecl

func (decls ImportDecls) PrintImports() string {
	seen := make(map[string]bool)
	var ss []string
	for _, decl := range decls {
		coqdecl := decl.CoqDecl()
		if !seen[coqdecl] {
			ss = append(ss, coqdecl)
			seen[coqdecl] = true
		}
	}
	sort.Strings(ss)
	return strings.Join(ss, "\n")
}

// File represents a complete Coq file (a sequence of declarations).
type File struct {
	ImportHeader string
	Footer       string
	PkgPath      string
	GoPackage    string
	Imports      ImportDecls
	Decls        []Decl
}

func (f File) autogeneratedNotice() CommentDecl {
	comment := fmt.Sprintf("autogenerated from %s", f.PkgPath)
	return CommentDecl(comment)
}

// Write outputs the Coq source for a File.
// noinspection GoUnhandledErrorResult
func (f File) Write(w io.Writer) {
	fmt.Fprintln(w, f.autogeneratedNotice().CoqDecl())
	fmt.Fprintln(w, strings.Trim(importHeader, "\n"))
	fmt.Fprintln(w, f.Imports.PrintImports())
	if len(f.Imports) > 0 {
		fmt.Fprintln(w)
	}
	fmt.Fprintln(w, f.ImportHeader)
	fmt.Fprintln(w)
	decls := make(map[string]bool)
	for i, d := range f.Decls {
		decl := d.CoqDecl()
		// don't translate the same thing twice (which the interface translation
		// can currently do)
		_, isComment := d.(CommentDecl)
		if isComment || !decls[decl] {
			fmt.Fprintln(w, decl)
			decls[decl] = true

			if i != len(f.Decls)-1 {
				fmt.Fprintln(w)
			}
		}
	}
	fmt.Fprint(w, f.Footer)
}
