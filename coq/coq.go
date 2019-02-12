package coq

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"strings"
	"unicode"

	"github.com/davecgh/go-spew/spew"
)

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	info *types.Info
	fset *token.FileSet
	errorReporter
	Config
}

type Config struct {
	AddSourceFileComments bool
}

func NewCtx(info *types.Info, fset *token.FileSet, config Config) Ctx {
	return Ctx{info: info,
		fset:          fset,
		errorReporter: newErrorReporter(fset),
		Config:        config,
	}
}

func (ctx Ctx) Where(node ast.Node) string {
	return ctx.fset.Position(node.Pos()).String()
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
	name    string
	Fields  []FieldDecl
	Comment string
}

func (d StructDecl) CoqDecl() string {
	var lines []string
	lines = append(lines, fmt.Sprintf("Module %s.", d.Name()))
	if d.Comment != "" {
		lines = append(lines,
			fmt.Sprintf("  (* %s *)", indent(5, d.Comment)))
	}
	lines = append(lines, "  Record t := mk {")
	for _, fd := range d.Fields {
		lines = append(lines, fmt.Sprintf("    %s: %s;", fd.Name, fd.Type.Coq()))
	}
	lines = append(lines, "  }.")
	lines = append(lines, fmt.Sprintf("End %s.", d.Name()))
	return strings.Join(lines, "\n")
}

func (d StructDecl) Name() string {
	return d.name
}

func getIdent(e ast.Expr) (ident string, ok bool) {
	if ident, ok := e.(*ast.Ident); ok {
		return ident.Name, true
	}
	return "", false
}

func isIdent(e ast.Expr, ident string) bool {
	i, ok := getIdent(e)
	return ok && i == ident
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
	return fmt.Sprintf("HashTable %s", addParens(t.Value.Coq()))
}

func (ctx Ctx) mapType(e *ast.MapType) MapType {
	switch k := e.Key.(type) {
	case *ast.Ident:
		if k.Name == "uint64" {
			return MapType{ctx.coqType(e.Value)}
		}
	default:
		ctx.Unsupported(k, "maps must be from uint64 (not %s)", spew.Sdump(k))
	}
	return MapType{}
}

func (ctx Ctx) selectorExprType(e *ast.SelectorExpr) TypeIdent {
	if isIdent(e.X, "filesys") && isIdent(e.Sel, "File") {
		return TypeIdent("Fd")
	}
	ctx.Unsupported(e, "selector for unknown type %s", spew.Sdump(e))
	return TypeIdent("<selector expr>")
}

func (ctx Ctx) coqTypeOfType(t types.Type) Type {
	switch t := t.(type) {
	case *types.Named:
		if _, ok := t.Underlying().(*types.Struct); ok {
			return StructName(t.Obj().Name())
		}
		return TypeIdent(t.Obj().Name())
	case *types.Struct:
		return StructName(t.String())
	case *types.Basic:
		return TypeIdent(t.Name())
	default:
		return TypeIdent("<type>")
	}
}

type ByteSliceType struct{}

func (t ByteSliceType) Coq() string {
	return "ByteSlice"
}

type SliceType struct {
	Value Type
}

func (t SliceType) Coq() string {
	return fmt.Sprintf("Slice %s", t.Value.Coq())
}

func (ctx Ctx) arrayType(e *ast.ArrayType) Type {
	if isIdent(e.Elt, "byte") {
		return ByteSliceType{}
	}
	return SliceType{ctx.coqType(e.Elt)}
}

func (ctx Ctx) coqType(e ast.Expr) Type {
	switch e := e.(type) {
	case *ast.Ident:
		return ctx.coqTypeOfType(ctx.info.TypeOf(e))
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.SelectorExpr:
		return ctx.selectorExprType(e)
	case *ast.ArrayType:
		return ctx.arrayType(e)
	default:
		ctx.NoExample(e, "unexpected type expr %s", spew.Sdump(e))
	}
	return TypeIdent("<type>")
}

func (ctx Ctx) fieldDecl(f *ast.Field) FieldDecl {
	if len(f.Names) > 1 {
		ctx.FutureWork(f, "multiple fields for same type (split them up)")
	}
	return FieldDecl{
		Name: f.Names[0].Name,
		Type: ctx.coqType(f.Type),
	}
}

func addSourceDoc(doc *ast.CommentGroup, comment *string) {
	if doc == nil {
		return
	}
	if *comment != "" {
		*comment += "\n\n"
	}
	*comment += stripTrailingNewline(doc.Text())
}

func (ctx Ctx) addSourceFile(node ast.Node, comment *string) {
	if !ctx.AddSourceFileComments {
		return
	}
	if *comment != "" {
		*comment += "\n\n   "
	}
	*comment += fmt.Sprintf("go: %s", ctx.Where(node))
}

func (ctx Ctx) typeDecl(doc *ast.CommentGroup, spec *ast.TypeSpec) StructDecl {
	if structTy, ok := spec.Type.(*ast.StructType); ok {
		ty := StructDecl{
			name: spec.Name.Name,
		}
		addSourceDoc(doc, &ty.Comment)
		ctx.addSourceFile(spec, &ty.Comment)
		for _, f := range structTy.Fields.List {
			ty.Fields = append(ty.Fields, ctx.fieldDecl(f))
		}
		return ty
	} else {
		ctx.Unsupported(spec, "non-struct type %s", spew.Sdump(spec))
	}
	return StructDecl{}
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

type ProjExpr struct {
	Projection string
	Arg        Expr
}

func addParens(s string) string {
	// conservative avoidance of parentheses
	if !strings.Contains(s, " ") {
		return s
	}
	return fmt.Sprintf("(%s)", s)
}

func (e ProjExpr) Coq() string {
	return fmt.Sprintf("%s.(%s)", addParens(e.Arg.Coq()), e.Projection)
}

func (s CallExpr) Coq() string {
	comps := []string{s.MethodName}
	for _, a := range s.Args {
		comps = append(comps, addParens(a.Coq()))
	}
	return strings.Join(comps, " ")
}

type ReturnExpr struct {
	Value Expr
}

func indent(spaces int, s string) string {
	repl := make([]byte, 1+spaces)
	repl[0] = '\n'
	for i := 1; i < len(repl); i++ {
		repl[i] = ' '
	}
	return strings.Replace(s, "\n", string(repl), -1)
}

func (e ReturnExpr) Coq() string {
	return "Ret " + indent(4, e.Value.Coq())
}

type Binding struct {
	Name string
	Expr Expr
}

func (b Binding) IsAnonymous() bool {
	return b.Name == ""
}

func toInitialLower(s string) string {
	pastFirstLetter := false
	return strings.Map(func(r rune) rune {
		if !pastFirstLetter {
			newR := unicode.ToLower(r)
			pastFirstLetter = true
			return newR
		}
		return r
	}, s)
}

func (ctx Ctx) methodExpr(f ast.Expr) string {
	switch f := f.(type) {
	case *ast.Ident:
		return f.Name
	case *ast.SelectorExpr:
		if isIdent(f.X, "fs") {
			return "FS." + toInitialLower(f.Sel.Name)
		}
		ctx.Unsupported(f.X, "cannot call methods selected from %s", spew.Sdump(f.X))
		return "<selector>"
	default:
		ctx.Unsupported(f, "call on expression %s", spew.Sdump(f))
	}
	return "<fun expr>"
}

// makeExpr parses a call to make() into the appropriate data-structure Call
func (ctx Ctx) makeExpr(args []ast.Expr) CallExpr {
	switch typeArg := args[0].(type) {
	case *ast.MapType:
		mapTy := ctx.mapType(typeArg)
		return CallExpr{
			MethodName: "Data.newHashTable",
			Args:       []Expr{mapTy.Value},
		}
	case *ast.ArrayType:
		if typeArg.Len != nil {
			ctx.Nope(typeArg, "can't make() arrays (only slices)")
		}
		ctx.Todo(typeArg, "array types are not really implemented")
		// TODO: need to check that slice is being initialized to an empty one
		elt := ctx.coqType(typeArg.Elt)
		return CallExpr{
			MethodName: "Data.newArray",
			Args:       []Expr{elt},
		}
	default:
		ctx.Nope(typeArg, "make() of %s, not a map or array", typeArg)
	}
	return CallExpr{}
}

func (ctx Ctx) callExpr(s *ast.CallExpr) CallExpr {
	call := CallExpr{}
	if isIdent(s.Fun, "make") {
		return ctx.makeExpr(s.Args)
	}
	call.MethodName = ctx.methodExpr(s.Fun)
	for _, arg := range s.Args {
		call.Args = append(call.Args, ctx.expr(arg))
	}
	return call
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

func structTypeFields(ty *types.Struct) []string {
	var fields []string
	for i := 0; i < ty.NumFields(); i++ {
		fields = append(fields, ty.Field(i).Name())
	}
	return fields
}

func (ctx Ctx) structSelector(e *ast.SelectorExpr) ProjExpr {
	structType := ctx.info.Selections[e].Recv().(*types.Named)
	proj := fmt.Sprintf("%s.%s", structType.Obj().Name(), e.Sel.Name)
	return ProjExpr{Projection: proj, Arg: ctx.expr(e.X)}
}

func (ctx Ctx) expr(e ast.Expr) Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return ctx.callExpr(e)
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.Ident:
		return IdentExpr(e.Name)
	case *ast.SelectorExpr:
		return ctx.structSelector(e)
	case *ast.CompositeLit:
		structType, ok := ctx.info.TypeOf(e).Underlying().(*types.Struct)
		if !ok {
			ctx.Unsupported(e, "non-struct literal %s", spew.Sdump(e))
		}
		structName, ok := getIdent(e.Type)
		if !ok {
			ctx.Nope(e.Type, "non-struct literal after type check")
		}
		lit := StructLiteral{StructName: structName}
		foundFields := make(map[string]bool)
		for _, el := range e.Elts {
			switch el := el.(type) {
			case *ast.KeyValueExpr:
				ident, ok := getIdent(el.Key)
				if !ok {
					ctx.NoExample(el.Key, "struct field keyed by non-identifier %+v", el.Key)
					return nil
				}
				lit.Elts = append(lit.Elts, FieldVal{
					Field: ident,
					Value: ctx.expr(el.Value),
				})
				foundFields[ident] = true
			default:
				// shouldn't be possible given type checking above
				ctx.Nope(el, "literal component in struct %s", spew.Sdump(e))
			}
		}
		for _, f := range structTypeFields(structType) {
			if !foundFields[f] {
				ctx.Unsupported(e, "incomplete struct literal %s", spew.Sdump(e))
			}
		}
		return lit
	default:
		// TODO: this probably has useful things (like map access)
		ctx.NoExample(e, "expr %s", spew.Sdump(e))
	}
	return nil
}

type TupleExpr []Expr

func (te TupleExpr) Coq() string {
	var comps []string
	for _, t := range te {
		comps = append(comps, t.Coq())
	}
	return fmt.Sprintf("(%s)", strings.Join(comps, ", "))
}

func mkTuple(es []Expr) Expr {
	if len(es) == 1 {
		return es[0]
	}
	return TupleExpr(es)
}

func (ctx Ctx) returnExpr(es []ast.Expr) Expr {
	var exprs TupleExpr
	for _, r := range es {
		exprs = append(exprs, ctx.expr(r))
	}
	return ReturnExpr{mkTuple(exprs)}
}

func anon(s Expr) Binding {
	return Binding{Name: "", Expr: s}
}

// A Block is a sequence of bindings, ending with some expression.
type BlockExpr struct {
	Bindings []Binding
}

func (be BlockExpr) Coq() string {
	var lines []string
	for n, b := range be.Bindings {
		if n == len(be.Bindings)-1 {
			// TODO: b.Expr.Coq() may need wrapping (eg, if it has newlines)
			//       We indent so at least it's visually apparent this has happened.
			lines = append(lines, indent(2, b.Expr.Coq()))
			continue
		}
		name := b.Name
		if b.IsAnonymous() {
			name = "_"
		}
		lines = append(lines, fmt.Sprintf("%s <- %s;", name, b.Expr.Coq()))
	}
	return strings.Join(lines, "\n")
}

func (ctx Ctx) blockStmt(s *ast.BlockStmt) BlockExpr {
	var bindings []Binding
	for _, s := range s.List {
		bindings = append(bindings, ctx.stmt(s))
	}
	return BlockExpr{bindings}
}

type IfExpr struct {
	Cond Expr
	Then Expr
	Else Expr
}

func (ife IfExpr) Coq() string {
	return fmt.Sprintf("if %s\n"+
		"  then (%s)\n"+
		"  else (%s)",
		ife.Cond.Coq(), indent(8, ife.Then.Coq()), indent(8, ife.Else.Coq()))
}

func (b Binding) Unwrap() (e Expr, ok bool) {
	if b.IsAnonymous() {
		return b.Expr, true
	}
	return nil, false
}

func (ctx Ctx) stmt(s ast.Stmt) Binding {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		return anon(ctx.returnExpr(s.Results))
	case *ast.ExprStmt:
		return anon(ctx.expr(s.X))
	case *ast.AssignStmt:
		if len(s.Lhs) > 1 {
			ctx.Unsupported(s, "multiple assignment")
		}
		if len(s.Rhs) != 1 {
			ctx.Nope(s, "assignment lengths should be equal")
		}
		lhs, rhs := s.Lhs[0], s.Rhs[0]
		if s.Tok != token.DEFINE {
			// NOTE: Do we need these? Should they become bindings anyway, or perhaps we should support let bindings?
			ctx.FutureWork(s, "re-assignments are not supported (only definitions")
		}
		ident, ok := getIdent(lhs)
		if !ok {
			ctx.Nope(lhs, "defining a non-identifier")
		}
		return Binding{Name: ident, Expr: ctx.expr(rhs)}
	case *ast.IfStmt:
		thenExpr, ok := ctx.stmt(s.Body).Unwrap()
		if !ok {
			ctx.Nope(s.Body, "if statement body ends with an assignment")
			return Binding{}
		}
		ife := IfExpr{
			Cond: ctx.expr(s.Cond),
			Then: thenExpr,
		}
		if s.Else == nil {
			ife.Else = ReturnExpr{IdentExpr("tt")}
		} else {
			elseExpr, ok := ctx.stmt(s.Else).Unwrap()
			if !ok {
				ctx.Nope(s.Else, "if statement else ends with an assignment")
				return Binding{}
			}
			ife.Else = elseExpr
		}
		return anon(ife)
	case *ast.ForStmt:
		ctx.Todo(s, "for statements")
	case *ast.BlockStmt:
		return anon(ctx.blockStmt(s))
	default:
		ctx.NoExample(s, "unexpected statement %s", spew.Sdump(s))
	}
	return Binding{}
}

// FuncDecl declares a function, including its parameters and body.
type FuncDecl struct {
	name       string
	Args       []FieldDecl
	ReturnType Type
	Body       Expr
	Comment    string
}

func (d FuncDecl) Name() string {
	return d.name
}

func (d FuncDecl) Signature() string {
	var args []string
	for _, a := range d.Args {
		args = append(args, a.CoqBinder())
	}
	return fmt.Sprintf("%s %s : proc %s",
		d.Name(), strings.Join(args, " "), d.ReturnType.Coq())
}

func (d FuncDecl) CoqDecl() string {
	var lines []string
	if d.Comment != "" {
		lines = append(lines, fmt.Sprintf("(* %s *)", d.Comment))
	}
	lines = append(lines, fmt.Sprintf("Definition %s :=", d.Signature()))
	lines = append(lines, fmt.Sprintf("  %s", indent(2, d.Body.Coq())))
	return strings.Join(lines, "\n")
}

// Decl is either a FuncDecl or StructDecl
type Decl interface {
	Name() string
	CoqDecl() string
}

type TupleType []Type

func mkTupleType(types []Type) Type {
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

func (ctx Ctx) returnType(results *ast.FieldList) Type {
	if results == nil {
		return TypeIdent("unit")
	}
	rs := results.List
	for _, r := range rs {
		if len(r.Names) > 0 {
			ctx.Unsupported(r, "named returned value")
			return TypeIdent("<invalid>")
		}
	}
	var ts []Type
	for _, r := range rs {
		if len(r.Names) > 0 {
			ctx.Unsupported(r, "named returned value")
			return TypeIdent("<invalid>")
		}
		ts = append(ts, ctx.coqType(r.Type))
	}
	return mkTupleType(ts)
}

func stripTrailingNewline(text string) string {
	if text == "" {
		return text
	}
	if text[len(text)-1] == '\n' {
		return text[:len(text)-1]
	}
	return text
}

func (ctx Ctx) funcDecl(d *ast.FuncDecl) FuncDecl {
	fd := FuncDecl{name: d.Name.Name}
	addSourceDoc(d.Doc, &fd.Comment)
	ctx.addSourceFile(d, &fd.Comment)
	if d.Recv != nil {
		ctx.FutureWork(d.Recv, "methods need to be lifted by moving the receiver to the arg list")
	}
	for _, p := range d.Type.Params.List {
		fd.Args = append(fd.Args, ctx.fieldDecl(p))
	}
	fd.ReturnType = ctx.returnType(d.Type.Results)
	fd.Body = ctx.blockStmt(d.Body)
	return fd
}

func (ctx Ctx) maybeDecl(d ast.Decl) Decl {
	switch d := d.(type) {
	case *ast.FuncDecl:
		fd := ctx.funcDecl(d)
		return fd
	case *ast.GenDecl:
		switch d.Tok {
		case token.IMPORT, token.CONST, token.VAR:
			return nil
		case token.TYPE:
			if len(d.Specs) > 1 {
				ctx.NoExample(d, "multiple specs in a type decl")
			}
			spec := d.Specs[0].(*ast.TypeSpec)
			ty := ctx.typeDecl(d.Doc, spec)
			return ty
		default:
			ctx.Nope(d, "unknown GenDecl token type for %s", spew.Sdump(d))
		}
	default:
		ctx.NoExample(d, "top-level decl %s", spew.Sdump(d))
	}
	return nil
}

func (ctx Ctx) FileDecls(fs []*ast.File) []Decl {
	var decls []Decl
	for _, f := range fs {
		for _, d := range f.Decls {
			if d := ctx.maybeDecl(d); d != nil {
				decls = append(decls, d)
			}
		}
	}
	return decls
}
