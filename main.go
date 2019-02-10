package main

import (
	"flag"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"strings"

	"github.com/davecgh/go-spew/spew"
)

// TODO: add (optional) comments to Coq output pointing to source

// TODO: copy comments attached to Go functions to Coq (low priority)

// FieldDecl is a name:type declaration (for a struct or function binders)
type FieldDecl struct {
	Name string
	Type Type
}

func (d FieldDecl) CoqBinder() string {
	return fmt.Sprintf("(%s:%s)", d.Name, d.Type)
}

// StructDecl is a Coq record for a Go struct
type StructDecl struct {
	name   string
	Fields []FieldDecl
}

func (d StructDecl) CoqDecl() string {
	var lines []string
	lines = append(lines, fmt.Sprintf("Module %s.", d.Name()))
	lines = append(lines, "  Record t := mk {")
	for _, fd := range d.Fields {
		lines = append(lines, fmt.Sprintf("    %s: %s;", fd.Name, fd.Type.Coq()))
	}
	lines = append(lines, "  }.")
	lines = append(lines, "End.")
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

func (ctx Ctx) coqType(e ast.Expr) Type {
	switch e := e.(type) {
	case *ast.Ident:
		return TypeIdent(e.Name)
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.SelectorExpr:
		return ctx.selectorExprType(e)
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

func (ctx Ctx) structDecl(spec *ast.TypeSpec) StructDecl {
	if structTy, ok := spec.Type.(*ast.StructType); ok {
		ty := StructDecl{name: spec.Name.Name}
		for _, f := range structTy.Fields.List {
			ty.Fields = append(ty.Fields, ctx.fieldDecl(f))
		}
		return ty
	} else {
		ctx.Unsupported(spec, "non-struct type %s", spew.Sdump(spec))
	}
	return StructDecl{}
}

// Ctx helps resolve struct info
type Ctx struct {
	Info *types.Info
	ErrorReporter
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

func (e ReturnExpr) Coq() string {
	return "Ret " + e.Value.Coq()
}

type Binding struct {
	Name string
	Expr Expr
}

func (b Binding) IsAnonymous() bool {
	return b.Name == ""
}

func anon(s Expr) Binding {
	return Binding{Name: "", Expr: s}
}

func (ctx Ctx) methodExpr(f ast.Expr) string {
	switch f := f.(type) {
	case *ast.Ident:
		return f.Name
	case *ast.SelectorExpr:
		if isIdent(f.X, "fs") {
			// TODO: lower-case name
			return "FS." + f.Sel.Name
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
			Args:       []Expr{mapTy},
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

func (ctx Ctx) callStmt(s *ast.CallExpr) CallExpr {
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

func (ctx Ctx) exprStmt(s *ast.ExprStmt) Binding {
	return anon(ctx.expr(s.X))
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
	for _, f := range s.Elts {
		field := fmt.Sprintf("%s.%s := %s;",
			s.StructName, f.Field, f.Value.Coq())
		pieces = append(pieces, field)
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
	structType := ctx.Info.Selections[e].Recv().(*types.Named)
	proj := fmt.Sprintf("%s.%s", structType.Obj().Name(), e.Sel.Name)
	return ProjExpr{Projection: proj, Arg: ctx.expr(e.X)}
}

func (ctx Ctx) expr(e ast.Expr) Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return ctx.callStmt(e)
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.Ident:
		return IdentExpr(e.Name)
	case *ast.SelectorExpr:
		return ctx.structSelector(e)
	case *ast.CompositeLit:
		structType, ok := ctx.Info.TypeOf(e).Underlying().(*types.Struct)
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

func (ctx Ctx) stmt(s ast.Stmt) Binding {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		if len(s.Results) > 1 {
			ctx.Unsupported(s, "multiple return")
		}
		return anon(ReturnExpr{ctx.expr(s.Results[0])})
	case *ast.ExprStmt:
		return ctx.exprStmt(s)
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
		if ident, ok := getIdent(lhs); ok {
			s := Binding{Name: ident, Expr: ctx.expr(rhs)}
			return s
		} else {
			ctx.Nope(lhs, "defining a non-identifier")
		}
	default:
		ctx.NoExample(s, "unexpected statement %s", spew.Sdump(s))
	}
	return Binding{}
}

// Block represents a sequence of bindings, ending with some expression.
//
// eventually may need to wrap a block in a recursive structure for if-statements and loops
type Block struct {
	// invariant: last binding is always anonymous
	Bindings []Binding
}

func NewBlock(bs []Binding) Block {
	lastBinding := bs[len(bs)-1]
	if !lastBinding.IsAnonymous() {
		return Block{}
	}
	return Block{bs}
}

func (ctx Ctx) blockStmt(s *ast.BlockStmt) Block {
	var bindings []Binding
	for _, s := range s.List {
		bindings = append(bindings, ctx.stmt(s))
	}
	return NewBlock(bindings)
}

// FuncDecl declares a function, including its parameters and body.
type FuncDecl struct {
	name       string
	Args       []FieldDecl
	ReturnType Type
	Body       Block
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
	lines = append(lines, fmt.Sprintf("Definition %s :=", d.Signature()))
	for n, b := range d.Body.Bindings {
		if n == len(d.Body.Bindings)-1 {
			lines = append(lines, fmt.Sprintf("  %s.", b.Expr.Coq()))
			continue
		}
		name := b.Name
		if b.IsAnonymous() {
			name = "_"
		}
		lines = append(lines, fmt.Sprintf("  %s <- %s;", name, b.Expr.Coq()))
	}
	return strings.Join(lines, "\n")
}

// Decl is either a FuncDecl or StructDecl
type Decl interface {
	Name() string
	CoqDecl() string
}

func (ctx Ctx) returnType(results *ast.FieldList) Type {
	if results == nil {
		return TypeIdent("unit")
	}
	rs := results.List
	if len(rs) > 1 {
		ctx.Unsupported(results, "multiple return values")
		return TypeIdent("<invalid>")
	}
	if len(rs[0].Names) > 0 {
		ctx.Unsupported(results, "named returned values")
		return TypeIdent("<invalid>")
	}
	return ctx.coqType(rs[0].Type)

}

func (ctx Ctx) funcDecl(d *ast.FuncDecl) FuncDecl {
	fd := FuncDecl{name: d.Name.Name}
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
			ty := ctx.structDecl(spec)
			return ty
		default:
			ctx.Nope(d, "unknown GenDecl token type for %s", spew.Sdump(d))
		}
	default:
		ctx.NoExample(d, "top-level decl %s", spew.Sdump(d))
	}
	return nil
}

func (ctx Ctx) fileDecls(fs []*ast.File) []Decl {
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

func main() {
	srcDir := flag.String("src", ".", "source directory")
	flag.Parse()
	if flag.NArg() < 1 {
		panic("Usage: goose <package name>")
	}
	packageName := flag.Arg(0)

	fset := token.NewFileSet()
	filter := func(os.FileInfo) bool { return true }
	packages, err := parser.ParseDir(fset, *srcDir, filter, parser.ParseComments)

	var files []*ast.File
	for _, f := range packages[packageName].Files {
		files = append(files, f)
	}

	conf := types.Config{Importer: importer.Default()}
	info := &types.Info{
		Defs:       make(map[*ast.Ident]types.Object),
		Uses:       make(map[*ast.Ident]types.Object),
		Types:      make(map[ast.Expr]types.TypeAndValue),
		Selections: make(map[*ast.SelectorExpr]*types.Selection),
	}
	_, err = conf.Check(packageName, fset, files, info)
	if err != nil {
		panic(err)
	}
	ctx := Ctx{Info: info, ErrorReporter: NewErrorReporter(fset)}
	for _, d := range ctx.fileDecls(files) {
		fmt.Println(d.CoqDecl())
		fmt.Println()
	}
}
