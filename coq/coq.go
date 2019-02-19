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
	repl := make([]byte, 1+spaces)
	repl[0] = '\n'
	for i := 1; i < len(repl); i++ {
		repl[i] = ' '
	}
	return strings.Replace(s, "\n", string(repl), -1)
}

// FieldDecl is a name:type declaration (for a struct or function binders)
type FieldDecl struct {
	Name string
	Type Type
}

func (d FieldDecl) CoqBinder() string {
	return fmt.Sprintf("(%s:%s)", d.Name, d.Type.Coq())
}

// StructDecl is a Coq record for a Go struct
type StructDecl struct {
	Name    string
	Fields  []FieldDecl
	Comment string
}

func (d StructDecl) CoqDecl() string {
	var pp buffer
	pp.Add("Module %s.", d.Name)
	pp.Indent(2)
	if d.Comment != "" {
		pp.Add("(* %s *)", d.Comment)
	}
	pp.Add("Record t := mk {")
	pp.Indent(2)
	for _, fd := range d.Fields {
		pp.Add("%s: %s;", fd.Name, fd.Type.Coq())
	}
	pp.Indent(-2)
	pp.Add("}.")
	var zeroValueArgs []string
	for range d.Fields {
		zeroValueArgs = append(zeroValueArgs, "(zeroValue _)")
	}
	pp.Add("Global Instance t_zero : HasGoZero t := mk %s.",
		strings.Join(zeroValueArgs, " "))
	pp.Indent(-2)
	pp.Add("End %s.", d.Name)
	return pp.Build()
}

type Type interface {
	Coq() string
}

type TypeIdent string

func (t TypeIdent) Coq() string {
	return string(t)
}

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

type IdentExpr string

func (e IdentExpr) Coq() string {
	return string(e)
}

// CallExpr includes primitives and references to other functions.
type CallExpr struct {
	MethodName string
	Args       []Expr
}

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
	return blocked("Ret ", addParens(e.Value.Coq()))
}

type Binding struct {
	Names []string
	Expr  Expr
}

func NewAnon(e Expr) Binding {
	return Binding{Expr: e}
}

func (b Binding) isAnonymous() bool {
	return len(b.Names) == 0
}

func (b Binding) Binder() string {
	if b.isAnonymous() {
		return "_"
	}
	if len(b.Names) == 1 {
		return b.Names[0]
	}
	return fmt.Sprintf("let! (%s)", strings.Join(b.Names, ", "))
}

type FieldVal struct {
	Field string
	Value Expr
}

type StructLiteral struct {
	StructName string
	Elts       []FieldVal
}

func (s StructLiteral) Coq() string {
	var pieces []string
	for i, f := range s.Elts {
		field := fmt.Sprintf("%s.%s := %s;",
			s.StructName, f.Field, f.Value.Coq())
		if i == 0 {
			pieces = append(pieces, field)
		} else {
			pieces = append(pieces, "   "+field)
		}
	}
	return fmt.Sprintf("{| %s |}", strings.Join(pieces, "\n"))
}

type IntLiteral struct {
	Value uint64
}

func (l IntLiteral) Coq() string {
	return fmt.Sprintf("%d", l.Value)
}

type StringLiteral struct {
	Value string
}

func (l StringLiteral) Coq() string {
	return fmt.Sprintf(`"%s"`, l.Value)
}

type BinOp int

const (
	OpPlus BinOp = iota
	OpMinus
	OpEquals
	OpLessThan
	OpGreaterThan
	OpAppend
)

type BinaryExpr struct {
	X  Expr
	Op BinOp
	Y  Expr
}

func (be BinaryExpr) Coq() string {
	switch be.Op {
	case OpLessThan:
		// TODO: should just have a binary operator for this in Coq
		return fmt.Sprintf("compare_to %s %s Lt",
			addParens(be.X.Coq()), addParens(be.Y.Coq()))
	case OpGreaterThan:
		return fmt.Sprintf("compare_to %s %s Gt",
			addParens(be.X.Coq()), addParens(be.Y.Coq()))
	}

	var binop string
	switch be.Op {
	case OpPlus:
		binop = "+"
	case OpMinus:
		binop = "-"
	case OpEquals:
		// note that this is not a boolean; shouldn't be a problem for a while
		// since we don't actually support Go booleans, only if-statements
		binop = "=="
	case OpAppend:
		binop = "++"
	default:
		panic("unknown binop")
	}
	return fmt.Sprintf("%s %s %s", be.X.Coq(), binop, be.Y.Coq())
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
	case BinaryExpr, PureCall, IntLiteral, StringLiteral:
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
		if isPure(b.Expr) {
			// this generates invalid code if the binder happens to be for multiple values
			// (which would only happen if we supported some pure function with multiple return values)
			pp.Add("let %s := %s in",
				b.Binder(), b.Expr.Coq())
		} else {
			pp.Add("%s <- %s;",
				b.Binder(), b.Expr.Coq())
		}
	}
	return pp.Build()
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
	pp.Add("if %s", ife.Cond.Coq())
	flowBranch(&pp, "then", ife.Then)
	flowBranch(&pp, "else", ife.Else)
	return pp.Build()
}

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

// currently restrict loops to return nothing
// good way to lift this restriction is to require loops to be at the end of the
// function and then support return inside a loop instead of break
type LoopRetExpr struct{}

func (e LoopRetExpr) Coq() string {
	return "LoopRet tt"
}

type LoopContinueExpr struct {
	// Value is the value to start the next loop with
	Value Expr
}

func (e LoopContinueExpr) Coq() string {
	return blocked("Continue ", addParens(e.Value.Coq()))
}

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

// Signature renders the function declaration's type signature for Coq
func (d FuncDecl) Signature() string {
	var args []string
	for _, a := range d.Args {
		args = append(args, a.CoqBinder())
	}
	return fmt.Sprintf("%s %s : proc %s",
		d.Name, strings.Join(args, " "),
		addParens(d.ReturnType.Coq()))
}

func (d FuncDecl) CoqDecl() string {
	var pp buffer
	if d.Comment != "" {
		pp.Add("(* %s *)", d.Comment)
	}
	pp.Add("Definition %s :=", d.Signature())
	pp.Indent(2)
	pp.AddLine(d.Body.Coq() + ".")
	return pp.Build()
}

// Decl is either a FuncDecl or StructDecl
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

const importHeader string = "From RecoveryRefinement.Goose Require Import base."

type File []Decl

func (decls File) Write(w io.Writer) {
	fmt.Fprintln(w, importHeader)
	fmt.Fprintln(w)
	for i, d := range decls {
		fmt.Fprintln(w, d.CoqDecl())
		if i != len(decls)-1 {
			fmt.Fprintln(w)
		}
	}
}
