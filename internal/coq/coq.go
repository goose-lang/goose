package coq

import (
	"fmt"
	"io"
	"strings"
)

func isWellBalanced(s string, lDelim string, rDelim string) bool {
	if strings.HasPrefix(s, lDelim) && strings.HasSuffix(s, rDelim) {
		return true
	}
	return false
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

func (pp *buffer) Block(prefix string, format string, args ...interface{}) {
	pp.AddLine(prefix + indent(len(prefix), fmt.Sprintf(format, args...)))
	pp.Indent(len(prefix))
}

func (pp buffer) Build() string {
	return strings.Join(pp.lines, "\n")
}

func blocked(prefix string, code string) string {
	var pp buffer
	pp.Block(prefix, "%s", code)
	return pp.Build()
}

func addParens(s string) string {
	// conservative avoidance of parentheses
	if !strings.Contains(s, " ") ||
		isWellBalanced(s, "(", ")") ||
		isWellBalanced(s, "{|", "|}") {
		return s
	}
	return fmt.Sprintf("(%s)", s)
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
	pp.Block("(* ", "%s *)", c)
	pp.Indent(-len("(* "))
}

func quote(s string) string {
	return `"` + s + `"`
}

// FieldDecl is a name:type declaration (for a struct or function binders)
type FieldDecl struct {
	Name string
	Type Type
}

func (d FieldDecl) CoqBinder() string {
	return quote(d.Name)
}

// StructDecl is a Coq record for a Go struct
type StructDecl struct {
	Name    string
	Fields  []FieldDecl
	Comment string
}

// CoqDecl implements the Decl interface
//
// For StructDecl this consists of several commands to wrap the record
// definition in a module, which nicely namespaces the record's field accessors.
// The pattern is slightly verbose, but not more so than prefixing fields with
// the record name anyway.
//
// Since records are auto-generated, they can also include boilerplate. For
// example, we currently define an instance for HasGoZero to give the Go zero
// value by emitting the right boilerplate (rather than Ltac/typeclass magic for
// example). We could do the same to implement `Settable`.
func (d StructDecl) CoqDecl() string {
	var pp buffer
	pp.Add("Module %s.", d.Name)
	pp.Indent(2)
	pp.AddComment(d.Comment)
	pp.Add("Definition S := mkStruct [")
	pp.Indent(2)
	var fieldList []string
	for _, fd := range d.Fields {
		fieldList = append(fieldList, quote(fd.Name))
	}
	pp.Add("%s", strings.Join(fieldList, "; "))
	pp.Indent(-2)
	pp.Add("].")
	var typeList []string
	for _, fd := range d.Fields {
		typeList = append(typeList, fd.Type.Coq())
	}
	pp.Add("Definition T: ty := %s.", strings.Join(typeList, " * "))
	pp.Add("Section fields.")
	pp.Indent(2)
	pp.Add("%s", "Context `{ext_ty: ext_types}.")
	for _, fd := range d.Fields {
		pp.Add("Definition %s := structF! S %s.", fd.Name, quote(fd.Name))
	}
	pp.Indent(-2)
	pp.Add("End fields.")
	pp.Indent(-2)
	pp.Add("End %s.", d.Name)
	return pp.Build()
}

// Type represents some Coq type.
//
// Structurally identical to Expr but serves as a nice annotation in the type
// system for where types are expected.
type Type interface {
	Coq() string
}

// TypeIdent is an identifier referencing a type.
//
// Much like the Type interface this is the same as Ident but signals that a Go
// type rather than a value is being referenced.
type TypeIdent string

func (t TypeIdent) Coq() string {
	return string(t)
}

// StructName refers to a struct type from its name.
//
// This is Type rather than an Expr.
type StructName string

func (t StructName) Coq() string {
	return string(t) + ".t"
}

type MapType struct {
	Value Type
}

func (t MapType) Coq() string {
	return fmt.Sprintf("Map %s", addParens(t.Value.Coq()))
}

type SliceType struct {
	Value Type
}

func (t SliceType) Coq() string {
	return fmt.Sprintf("slice.t %s", addParens(t.Value.Coq()))
}

type Expr interface {
	Coq() string
}

// IdentExpr is an identifier expression.
type IdentExpr string

func (e IdentExpr) Coq() string {
	return quote(string(e))
}

// CallExpr includes primitives and references to other functions.
type CallExpr struct {
	MethodName string
	Args       []Expr
}

// NewCallExpr is a convenience to construct a CallExpr statically, especially
// for a fixed number of arguments.
func NewCallExpr(name string, args ...Expr) CallExpr {
	return CallExpr{MethodName: name, Args: args}
}

func (s CallExpr) Coq() string {
	comps := []string{s.MethodName}
	for _, a := range s.Args {
		comps = append(comps, addParens(a.Coq()))
	}
	return strings.Join(comps, " ")
}

// PureCall is a wrapper for a call to mark it as a pure expression.
type PureCall CallExpr

func (s PureCall) Coq() string {
	return CallExpr(s).Coq()
}

// ProjExpr is a record projection
//
// Projections could always be written using normal function call syntax, but
// using record syntax for projections makes code look nicer.
type ProjExpr struct {
	Projection string
	Arg        Expr
}

func (e ProjExpr) Coq() string {
	return fmt.Sprintf("%s.(%s)", addParens(e.Arg.Coq()), e.Projection)
}

type ReturnExpr struct {
	Value Expr
}

func (e ReturnExpr) Coq() string {
	return e.Value.Coq()
}

// Binding is a Coq binding (a part of a Bind expression)
//
// Note that a Binding is not an Expr. This is because emitting a binding
// requires knowing if it is the last binding in a sequence (in which case no
// binder should be written). A more accurate representation would be a cons
// representation, but this recursive structure is more awkward to work with; in
// practice delying handling the special last-binding to printing time is
// easier.
type Binding struct {
	// Names is a list to support anonymous and tuple-destructuring bindings.
	//
	// If Names is an empty list the binding is anonymous.
	//
	// If len(Names) > 1 then the binding uses the `let! p <- f; rx` notation,
	// exploiting a pattern in `p` to destructure a tuple.
	Names []string
	Expr  Expr
}

// NewAnon constructs an anonymous binding for an expression.
func NewAnon(e Expr) Binding {
	return Binding{Expr: e}
}

func (b Binding) isAnonymous() bool {
	return len(b.Names) == 0
}

// Binder emits the appropriate binder part of a binding, handling anonymous and
// tuple-destructuring forms.
func (b Binding) Binder() string {
	if b.isAnonymous() {
		return "_"
	}
	if len(b.Names) == 1 {
		return b.Names[0]
	}
	return fmt.Sprintf("let! (%s)", strings.Join(b.Names, ", "))
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
	StructName string
	elts       []fieldVal
}

// NewStructLiteral creates a StructLiteral with no values.
func NewStructLiteral(structName string) StructLiteral {
	return StructLiteral{StructName: structName}
}

// AddField appends a new (field, val) pair to a StructLiteral.
func (sl *StructLiteral) AddField(field string, value Expr) {
	sl.elts = append(sl.elts, fieldVal{field, value})
}

func (sl StructLiteral) Coq() string {
	var pp buffer
	pp.Add("buildStruct %s.S [", sl.StructName)
	pp.Indent(2)
	for _, f := range sl.elts {
		pp.Add("%s ::= %s;", quote(f.Field), f.Value.Coq())
	}
	pp.Indent(-2)
	pp.Add("]")
	return pp.Build()
}

type BoolLiteral bool

var True, False BoolLiteral = true, false

func (b BoolLiteral) Coq() string {
	if b {
		return "#true"
	} else {
		return "#false"
	}
}

type UnitLiteral struct{}

var Tt UnitLiteral = struct{}{}

func (tt UnitLiteral) Coq() string {
	return "#()"
}

type IntLiteral struct {
	Value uint64
}

func (l IntLiteral) Coq() string {
	return fmt.Sprintf("#%d", l.Value)
}

type StringLiteral struct {
	Value string
}

func (l StringLiteral) Coq() string {
	return fmt.Sprintf(`"%s"`, l.Value)
}

// BinOp is an enum for a Coq binary operator
type BinOp int

// Constants for the supported Coq binary operators
const (
	OpPlus BinOp = iota
	OpMinus
	OpEquals
	OpLessThan
	OpGreaterThan
	OpLessEq
	OpGreaterEq
	OpAppend
	OpMul
)

type BinaryExpr struct {
	X  Expr
	Op BinOp
	Y  Expr
}

func (be BinaryExpr) Coq() string {
	coqBinOp := map[BinOp]string{
		OpPlus:        "+",
		OpMinus:       "-",
		OpEquals:      "=",
		OpAppend:      "++",
		OpMul:         "*",
		OpLessThan:    "<",
		OpGreaterThan: ">",
		OpLessEq:      "≤",
		OpGreaterEq:   "≥",
	}
	if binop, ok := coqBinOp[be.Op]; ok {
		return fmt.Sprintf("%s %s %s", be.X.Coq(), binop, be.Y.Coq())
	}

	panic(fmt.Sprintf("unknown binop %d", be.Op))
}

type NotExpr struct {
	X Expr
}

func (e NotExpr) Coq() string {
	return fmt.Sprintf("negb %s", addParens(e.X.Coq()))
}

type TupleExpr []Expr

func (te TupleExpr) Coq() string {
	var comps []string
	for _, t := range te {
		comps = append(comps, t.Coq())
	}
	return fmt.Sprintf("(%s)",
		indent(1, strings.Join(comps, ", ")))
}

// NewTuple is a smart constructor that wraps multiple expressions in a TupleExpr
func NewTuple(es []Expr) Expr {
	if len(es) == 1 {
		return es[0]
	}
	return TupleExpr(es)
}

// A BlockExpr is a sequence of bindings, ending with some expression.
type BlockExpr struct {
	Bindings []Binding
}

func isPure(e Expr) bool {
	switch e.(type) {
	case BinaryExpr, PureCall, IntLiteral, StringLiteral, StructLiteral, ProjExpr:
		return true
	case CallExpr: // distinct from PureCall
		return false
	default:
		return false
	}
}

func (be BlockExpr) Coq() string {
	var pp buffer
	for n, b := range be.Bindings {
		if n == len(be.Bindings)-1 {
			pp.AddLine(b.Expr.Coq())
			continue
		}
		if b.isAnonymous() {
			pp.Add("%s;;", b.Expr.Coq())
		} else if len(b.Names) == 1 {
			pp.Add("let: %s := %s in", quote(b.Names[0]), b.Expr.Coq())
		} else {
			panic("TODO: go_lang destructuring notation")
		}
	}
	return pp.Build()
}

type DerefExpr struct {
	X Expr
}

func (e DerefExpr) Coq() string {
	return "!" + e.X.Coq()
}

type StoreStmt struct {
	Dst Expr
	X   Expr
}

func (e StoreStmt) Coq() string {
	return fmt.Sprintf("%s <- %s", e.Dst, e.X)
}

type IfExpr struct {
	Cond Expr
	Then Expr
	Else Expr
}

func flowBranch(pp *buffer, prefix string, e Expr) {
	code := e.Coq()
	if !strings.ContainsRune(code, '\n') {
		// compact, single-line form
		pp.Block(prefix+" ", "%s", code)
		pp.Indent(-(len(prefix) + 1))
		return
	}
	// full multiline, nicely indented form
	pp.AddLine(prefix)
	pp.Indent(2)
	pp.AddLine(code)
	pp.Indent(-2)
}

func (ife IfExpr) Coq() string {
	var pp buffer
	pp.Add("if: %s", ife.Cond.Coq())
	flowBranch(&pp, "then", ife.Then)
	flowBranch(&pp, "else", ife.Else)
	return pp.Build()
}

// Unwrap returns the expression in a Binding expected to be anonymous.
func (b Binding) Unwrap() (e Expr, ok bool) {
	if b.isAnonymous() {
		return b.Expr, true
	}
	return nil, false
}

type HashTableInsert struct {
	Value Expr
}

func (e HashTableInsert) Coq() string {
	return fmt.Sprintf("(fun _ => Some %s)", addParens(e.Value.Coq()))
}

// A LoopRetExpr breaks out of a loop.
//
// The Loop constructor in proc permits returning a value (of an arbitrary type)
// when breaking, but we don't support that here.
//
// We could support returning something for loops at the end of a function,
// where a Go `return` would correspond to a Coq `LoopRet`. function and then
// support return inside a loop instead of break
type LoopRetExpr struct{}

func (e LoopRetExpr) Coq() string {
	return "LoopRet tt"
}

// A LoopContinueExpr moves to the next iteration in a loop.
type LoopContinueExpr struct {
	// Value is the value to start the next loop with
	Value Expr
}

func (e LoopContinueExpr) Coq() string {
	return blocked("Continue ", addParens(e.Value.Coq()))
}

// A LoopExpr is a complete Coq loop
//
// Loops are allowed any type for loop variables (although there's no way to
// express the unit type or value for the loop variable).
type LoopExpr struct {
	// name of loop variable
	LoopVarIdent string
	// the initial loop variable value to use
	Initial Expr
	// the body of the loop, with LoopVarIdent as a free variable
	Body BlockExpr
}

func (e LoopExpr) Coq() string {
	var pp buffer
	pp.Block("Loop (", "fun %s =>", e.LoopVarIdent)
	pp.Add("%s) %s",
		e.Body.Coq(),
		addParens(e.Initial.Coq()))
	return pp.Build()
}

// MapIterExpr is a call to the map iteration helper.
//
// The Coq support for this call handles the looping, and happens to do so with
// finite iteration over a list rather than a Loop (although this is unimportant
// to emitting a correct call to Data.mapIter).
type MapIterExpr struct {
	// name of key and value identifiers
	KeyIdent, ValueIdent string
	// map to iterate over
	Map Expr
	// body of loop, with KeyIdent and ValueIdent as free variables
	Body BlockExpr
}

func (e MapIterExpr) Coq() string {
	var pp buffer
	pp.Add("Data.mapIter %s (fun %s %s =>",
		e.Map, e.KeyIdent, e.ValueIdent)
	pp.Indent(2)
	pp.Add("%s)", e.Body.Coq())
	return pp.Build()
}

// SpawnExpr is a call to Spawn a thread running a procedure.
//
// The body can capture variables in the environment.
type SpawnExpr struct {
	Body BlockExpr
}

func (e SpawnExpr) Coq() string {
	var pp buffer
	pp.Block("Spawn (", "%s)", e.Body.Coq())
	return pp.Build()
}

// FuncDecl declares a function, including its parameters and body.
type FuncDecl struct {
	Name       string
	Args       []FieldDecl
	ReturnType Type
	Body       Expr
	Comment    string
}

// Signature renders the function declaration's bindings
func (d FuncDecl) Signature() string {
	var args []string
	for _, a := range d.Args {
		args = append(args, a.CoqBinder())
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
	pp.Add("Definition %s: val :=", d.Name)
	pp.Indent(2)
	pp.Add("λ: %s,", d.Signature())
	pp.Indent(2)
	pp.AddLine(d.Body.Coq() + ".")
	return pp.Build()
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

type ConstDecl struct {
	Name    string
	Type    Type
	Val     Expr
	Comment string
}

func (d ConstDecl) CoqDecl() string {
	var pp buffer
	pp.AddComment(d.Comment)
	pp.Block("Definition ", "%s : %s := %s.",
		d.Name, d.Type.Coq(), d.Val.Coq())
	return pp.Build()
}

// Decl is a FuncDecl, StructDecl, CommentDecl, or ConstDecl
type Decl interface {
	CoqDecl() string
}

type TupleType []Type

// NewTupleType is a smart constructor that wraps multiple types in a TupleType
func NewTupleType(types []Type) Type {
	if len(types) == 1 {
		return types[0]
	}
	return TupleType(types)
}

func (tt TupleType) Coq() string {
	var comps []string
	for _, t := range tt {
		comps = append(comps, t.Coq())
	}
	return fmt.Sprintf("(%s)", strings.Join(comps, " * "))
}

type PtrType struct {
	Value Type
}

func (t PtrType) Coq() string {
	return "ptr " + addParens(t.Value.Coq())
}

// TODO: note that the second two lines should be customized depending on the
//  target interface.
const importHeader string = `
From Perennial.go_lang Require Import prelude.

(* disk FFI *)
From Perennial.go_lang Require Import ffi.disk.
Existing Instances disk_op disk_model disk_ty.
Local Coercion Var' (s: string) := Var s.
`

// File represents a complete Coq file (a sequence of declarations).
type File struct {
	GoPackage string
	Decls     []Decl
}

func (f File) autogeneratedNotice() CommentDecl {
	comment := fmt.Sprintf("autogenerated from %s", f.GoPackage)
	return CommentDecl(comment)
}

// Write outputs the Coq source for a File.
//noinspection GoUnhandledErrorResult
func (f File) Write(w io.Writer) {
	fmt.Fprintln(w, f.autogeneratedNotice().CoqDecl())
	fmt.Fprintln(w, strings.Trim(importHeader, "\n"))
	fmt.Fprintln(w)
	for i, d := range f.Decls {
		fmt.Fprintln(w, d.CoqDecl())
		if i != len(f.Decls)-1 {
			fmt.Fprintln(w)
		}
	}
}
