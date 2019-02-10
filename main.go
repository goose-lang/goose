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

// FieldDecl is a name:type declaration (for a struct)
type FieldDecl struct {
	Name string
	Type string
}

// StructType is a Coq record for a Go struct
type StructType struct {
	Name   string
	Fields []FieldDecl
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

type MapType string

func (t MapType) Coq() string {
	return fmt.Sprintf("HashTable %s ", string(t))
}

func (ctx Ctx) mapType(e *ast.MapType) MapType {
	switch k := e.Key.(type) {
	case *ast.Ident:
		if k.Name == "uint64" {
			return MapType(ctx.typeToCoq(e.Value))
		}
	default:
		ctx.Unsupported(k,"maps must be from uint64 (not %s)", spew.Sdump(k))
	}
	return "<bad hashtable>"
}

func (ctx Ctx) selectorExprType(e *ast.SelectorExpr) string {
	if isIdent(e.X, "filesys") && isIdent(e.Sel,"File") {
		return "Fd"
	}
	ctx.Unsupported(e,"selector for unknown type %s", spew.Sdump(e))
	return "<selector expr>"
}

func (ctx Ctx) typeToCoq(e ast.Expr) string {
	switch e := e.(type) {
	case *ast.Ident:
		return e.Name
	case *ast.MapType:
		return ctx.mapType(e).Coq()
	case *ast.SelectorExpr:
		return ctx.selectorExprType(e)
	default:
		ctx.NoExample(e,"unexpected type expr %s", spew.Sdump(e))
	}
	return "<type>"
}

func (ctx Ctx) fieldDecl(f *ast.Field) FieldDecl {
	if len(f.Names) > 1 {
		ctx.FutureWork(f,"multiple fields for same type (split them up)")
	}
	return FieldDecl{
		Name: f.Names[0].Name,
		Type: ctx.typeToCoq(f.Type),
	}
}

func (ctx Ctx) structType(name string, structTy *ast.StructType) StructType {
	ty := StructType{Name: name}
	for _, f := range structTy.Fields.List {
		ty.Fields = append(ty.Fields, ctx.fieldDecl(f))
	}
	return ty
}

func (ctx Ctx) structDecl(spec *ast.TypeSpec) StructType {
	if structTy, ok := spec.Type.(*ast.StructType); ok {
		ty := ctx.structType(spec.Name.Name, structTy)
		return ty
	} else {
		ctx.Unsupported(spec,"non-struct type %s", spew.Sdump(spec))
	}
	return StructType{}
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

func (s CallExpr) Coq() string {
	comps := []string{s.MethodName}
	for _, a := range s.Args {
		comps = append(comps, a.Coq())
	}
	return strings.Join(comps, " ")
}

// TODO: this arrangement of statements and expressions is bizarre and wrong;
// write a proper hierarchy and enforce it with marker methods.

type ReturnStmt struct {
	Value Expr
}

// Stmt is an Expr or ReturnStmt
type Stmt interface {
}

type Binding struct {
	Name string
	Stmt
}

func anon(s Stmt) Binding {
	return Binding{Name: "", Stmt: s}
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
		ctx.Unsupported(f,"call on expression %s", spew.Sdump(f))
	}
	return "<fun expr>"
}

func (ctx Ctx) callStmt(s *ast.CallExpr) CallExpr {
	call := CallExpr{}
	// TODO: treat calls to "make" specially
	call.MethodName = ctx.methodExpr(s.Fun)
	for _, arg := range s.Args {
		call.Args = append(call.Args, ctx.expr(arg))
	}
	return call
}

func (ctx Ctx) exprStmt(s *ast.ExprStmt) Stmt {
	return ctx.expr(s.X)
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

func (ctx Ctx) expr(e ast.Expr) Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return ctx.callStmt(e)
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.Ident:
		return IdentExpr(e.Name)
	case *ast.SelectorExpr:
		structType := ctx.Info.Selections[e].Recv().(*types.Named)
		return IdentExpr(fmt.Sprintf("%s.%s", structType.Obj().Name(), e.Sel.Name))
	case *ast.CompositeLit:
		structType, ok := ctx.Info.TypeOf(e).Underlying().(*types.Struct)
		if !ok {
			ctx.Unsupported(e,"non-struct literal %s", spew.Sdump(e))
		}
		lit := StructLiteral{StructName: ctx.typeToCoq(e.Type)}
		foundFields := make(map[string]bool)
		for _, el := range e.Elts {
			switch el := el.(type) {
			case *ast.KeyValueExpr:
				ident, ok := getIdent(el.Key)
				if !ok {
					ctx.NoExample(el.Key,"struct field keyed by non-identifier %+v", el.Key)
					return nil
				}
				lit.Elts = append(lit.Elts, FieldVal{
					Field: ident,
					Value: ctx.expr(el.Value),
				})
				foundFields[ident] = true
			default:
				// shouldn't be possible given type checking above
				ctx.Docs(el,"literal component in struct %s", spew.Sdump(e))
			}
		}
		for _, f := range structTypeFields(structType) {
			if !foundFields[f] {
				ctx.Unsupported(e,"incomplete struct literal %s", spew.Sdump(e))
			}
		}
		return lit
	default:
		// TODO: this probably has useful things (like map access)
		ctx.NoExample(e,"expr %s", spew.Sdump(e))
	}
	return nil
}

func (ctx Ctx) stmt(s ast.Stmt) Binding {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		if len(s.Results) > 1 {
			ctx.Unsupported(s,"multiple return")
		}
		return anon(ReturnStmt{ctx.expr(s.Results[0])})
	case *ast.ExprStmt:
		return anon(ctx.exprStmt(s))
	case *ast.AssignStmt:
		if len(s.Lhs) > 1 {
			ctx.Unsupported(s,"multiple assignment")
		}
		if len(s.Rhs) != 1 {
			ctx.Docs(s,"assignment lengths should be equal")
		}
		lhs, rhs := s.Lhs[0], s.Rhs[0]
		if s.Tok != token.DEFINE {
			// NOTE: Do we need these? Should they become bindings anyway, or perhaps we should support let bindings?
			ctx.FutureWork(s,"re-assignments are not supported (only definitions")
		}
		if ident, ok := getIdent(lhs); ok {
			s := Binding{Name: ident, Stmt: ctx.expr(rhs)}
			return s
		} else {
			ctx.Docs(lhs,"defining a non-identifier")
		}
	default:
		ctx.NoExample(s,"unexpected statement %s", spew.Sdump(s))
	}
	return Binding{}
}

func (ctx Ctx) blockStmt(s *ast.BlockStmt) BindingSeq {
	var bindings []Binding
	for _, s := range s.List {
		bindings = append(bindings, ctx.stmt(s))
	}
	return BindingSeq(bindings)
}

type BindingSeq []Binding

// FuncDecl declares a function, including its parameters and body.
type FuncDecl struct {
	Name       string
	Args       []FieldDecl
	ReturnType string
	Body       BindingSeq
}

func (ctx Ctx) returnType(results *ast.FieldList) string {
	if results == nil {
		return "unit"
	}
	rs := results.List
	if len(rs) > 1 {
		ctx.Unsupported(results,"multiple return values")
	}
	if len(rs[0].Names) > 0 {
		ctx.Unsupported(results,"named returned values")
	}
	return ctx.typeToCoq(rs[0].Type)

}

func (ctx Ctx) funcDecl(d *ast.FuncDecl) FuncDecl {
	fd := FuncDecl{Name: d.Name.Name}
	if d.Recv != nil {
		ctx.FutureWork(d.Recv,"methods need to be lifted by moving the receiver to the arg list")
	}
	for _, p := range d.Type.Params.List {
		fd.Args = append(fd.Args, ctx.fieldDecl(p))
	}
	fd.ReturnType = ctx.returnType(d.Type.Results)
	fd.Body = ctx.blockStmt(d.Body)
	return fd
}

// TODO: make this return declarations rather than tracing
func (ctx Ctx) traceDecls(ds []ast.Decl) {
	for _, d := range ds {
		switch d := d.(type) {
		case *ast.FuncDecl:
			fd := ctx.funcDecl(d)
			fmt.Printf("func %s\n", d.Name.Name)
			fmt.Printf("%+v", fd)
		case *ast.GenDecl:
			switch d.Tok {
			case token.IMPORT, token.CONST, token.VAR:
				continue
			case token.TYPE:
				if len(d.Specs) > 1 {
					ctx.NoExample(d, "multiple specs in a type decl")
				}
				spec := d.Specs[0].(*ast.TypeSpec)
				ty := ctx.structDecl(spec)
				fmt.Printf("type %s\n", ty.Name)
				fmt.Printf("%+v", ty)
			default:
				ctx.Docs(d,"unknown gendecl token type for %+v", d)
			}
		default:
			ctx.NoExample(d,"top-level decl %s", spew.Sdump(d))
		}
		fmt.Printf("\n\n")
	}
}

func (ctx Ctx) traceFiles(fs []*ast.File) {
	for _, f := range fs {
		ctx.traceDecls(f.Decls)
	}
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
	packages, err := parser.ParseDir(fset, *srcDir, filter, parser.Mode(0))

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
	_, err = conf.Check("simpledb", fset, files, info)
	if err != nil {
		panic(err)
	}
	ctx := Ctx{Info: info, ErrorReporter: NewErrorReporter(fset)}
	ctx.traceFiles(files)
}
