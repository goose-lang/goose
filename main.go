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
	switch e := e.(type) {
	case *ast.Ident:
		return e.Name, true
	default:
		return "", false
	}
}

func isIdent(e ast.Expr, ident string) bool {
	i, ok := getIdent(e)
	return ok && i == ident
}

type MapType string

func (t MapType) Coq() string {
	return fmt.Sprintf("HashTable %s ", string(t))
}

func mapType(e *ast.MapType) MapType {
	switch k := e.Key.(type) {
	case *ast.Ident:
		if k.Name == "uint64" {
			return MapType(typeToCoq(e.Value))
		}
	default:
	}
	error.Unhandled("maps must be from uint64")
	return "<bad hashtable>"
}

func selectorExprType(e *ast.SelectorExpr) string {
	if isIdent(e.X, "filesys") &&
		e.Sel != nil && e.Sel.Name == "File" {
		return "Fd"
	}
	error.Unhandled("selector for unknown type %s", spew.Sdump(e))
	return "<selector expr>"
}

func typeToCoq(e ast.Expr) string {
	switch e := e.(type) {
	case *ast.Ident:
		return e.Name
	case *ast.MapType:
		return mapType(e).Coq()
	case *ast.SelectorExpr:
		return selectorExprType(e)
	default:
	}
	error.NoExample("unexpected type expr %s", spew.Sdump(e))
	return "<type>"
}

func fieldDecl(f *ast.Field) FieldDecl {
	if len(f.Names) > 1 {
		error.FutureWork("multiple fields for same type (split them up)")
	}
	return FieldDecl{
		Name: f.Names[0].Name,
		Type: typeToCoq(f.Type),
	}
}

func structDecl(name string, structTy *ast.StructType) StructType {
	ty := StructType{Name: name}
	for _, f := range structTy.Fields.List {
		ty.Fields = append(ty.Fields, fieldDecl(f))
	}
	return ty
}

// Structs helps resolve struct info
type Structs struct {
	Declarations []StructType
	Fields       map[*types.Var]*StructType
	Info         *types.Info
}

func NewStructs(info *types.Info) Structs {
	return Structs{Fields: make(map[*types.Var]*StructType), Info: info}
}

func (sinfo *Structs) AddStruct(spec *ast.TypeSpec) StructType {
	if structTy, ok := spec.Type.(*ast.StructType); ok {
		ty := structDecl(spec.Name.Name, structTy)
		sinfo.Declarations = append(sinfo.Declarations, ty)
		// TODO: what do we do with spec.Name to later find this struct?
		return ty
	} else {
		error.Unhandled("non-struct type %s", spec.Name.Name)
	}
	return StructType{}
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

func methodExpr(f ast.Expr) string {
	switch f := f.(type) {
	case *ast.Ident:
		return f.Name
	case *ast.SelectorExpr:
		if isIdent(f.X, "fs") {
			// TODO: lower-case name
			return "FS." + f.Sel.Name
		}
		error.Unhandled("cannot call methods selected from %s", spew.Sdump(f.X))
		return "<selector>"
	default:
		error.Unhandled("call on expression %s", spew.Sdump(f))
	}
	return "<fun expr>"
}

func (sinfo Structs) callStmt(s *ast.CallExpr) CallExpr {
	call := CallExpr{}
	call.MethodName = methodExpr(s.Fun)
	for _, arg := range s.Args {
		call.Args = append(call.Args, sinfo.expr(arg))
	}
	return call
}

func (sinfo Structs) exprStmt(s *ast.ExprStmt) Stmt {
	return sinfo.expr(s.X)
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

func (sinfo Structs) expr(e ast.Expr) Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return sinfo.callStmt(e)
	case *ast.MapType:
		return mapType(e)
	case *ast.Ident:
		return IdentExpr(e.Name)
	case *ast.SelectorExpr:
		structType := sinfo.Info.Selections[e].Recv().(*types.Named)
		return IdentExpr(fmt.Sprintf("%s.%s", structType.Obj().Name(), e.Sel.Name))
	case *ast.CompositeLit:
		if e.Incomplete {
			error.Unhandled("incomplete struct literals are unsupported")
		}
		lit := StructLiteral{StructName: typeToCoq(e.Type)}
		for _, el := range e.Elts {
			switch el := el.(type) {
			case *ast.KeyValueExpr:
				ident, ok := getIdent(el.Key)
				if !ok {
					error.NoExample("struct field keyed by non-identifier %+v", el.Key)
					return nil
				}
				lit.Elts = append(lit.Elts, FieldVal{
					Field: ident,
					Value: sinfo.expr(el.Value),
				})
			default:
				error.Unhandled("non-struct literal %s", spew.Sdump(e))
			}
		}
		return lit
	default:
		// TODO: this probably has useful things (like map access)
		error.NoExample("expr %s", spew.Sdump(e))
	}
	return nil
}

func (sinfo Structs) stmt(s ast.Stmt) Binding {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		if len(s.Results) > 1 {
			error.Unhandled("multiple return")
		}
		return anon(ReturnStmt{sinfo.expr(s.Results[0])})
	case *ast.ExprStmt:
		return anon(sinfo.exprStmt(s))
	case *ast.AssignStmt:
		if len(s.Lhs) > 1 {
			error.Unhandled("multiple assignment")
		}
		if len(s.Rhs) != 1 {
			error.Docs("assignment lengths should be equal")
		}
		if s.Tok != token.DEFINE {
			// NOTE: Do we need these? Should they become bindings anyway, or perhaps we should support let bindings?
			error.FutureWork("re-assignments are not supported (only definitions")
		}
		if ident, ok := getIdent(s.Lhs[0]); ok {
			s := Binding{Name: ident, Stmt: sinfo.expr(s.Rhs[0])}
			return s
		} else {
			error.Docs("defining a non-identifier")
		}
	default:
		error.NoExample("unexpected statement %s", spew.Sdump(s))
	}
	return Binding{}
}

func (sinfo Structs) blockStmt(s *ast.BlockStmt) BindingSeq {
	var bindings []Binding
	for _, s := range s.List {
		bindings = append(bindings, sinfo.stmt(s))
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

func returnType(results *ast.FieldList) string {
	if results == nil {
		return "unit"
	}
	rs := results.List
	if len(rs) > 1 {
		error.Unhandled("multiple return values")
	}
	if len(rs[0].Names) > 0 {
		error.Unhandled("named returned values")
	}
	return typeToCoq(rs[0].Type)

}

func (sinfo Structs) funcDecl(d *ast.FuncDecl) FuncDecl {
	fd := FuncDecl{Name: d.Name.Name}
	if d.Recv != nil {
		error.FutureWork("methods need to be lifted by moving the receiver to the arg list")
	}
	for _, p := range d.Type.Params.List {
		fd.Args = append(fd.Args, fieldDecl(p))
	}
	fd.ReturnType = returnType(d.Type.Results)
	fd.Body = sinfo.blockStmt(d.Body)
	return fd
}

func traceDecls(info *types.Info, ds []ast.Decl) {
	sinfo := NewStructs(info)
	for _, d := range ds {
		switch d := d.(type) {
		case *ast.FuncDecl:
			continue
		case *ast.GenDecl:
			switch d.Tok {
			case token.IMPORT, token.CONST, token.VAR:
				continue
			case token.TYPE:
				if len(d.Specs) > 1 {
					error.NoExample("multiple specs in a type decl")
				}
				spec := d.Specs[0].(*ast.TypeSpec)
				ty := sinfo.AddStruct(spec)
				fmt.Printf("type %s\n", ty.Name)
				fmt.Printf("%+v", ty)
			default:
				error.Docs("unknown gendecl token type for %+v", d)
			}
		default:
			error.NoExample("top-level decl %s", spew.Sdump(d))
		}
		fmt.Printf("\n\n")
	}
	for _, d := range ds {
		switch d := d.(type) {
		case *ast.FuncDecl:
			fd := sinfo.funcDecl(d)
			fmt.Printf("func %s\n", d.Name.Name)
			fmt.Printf("%+v", fd)
		default:
			continue
		}
		fmt.Printf("\n\n")
	}
}

func traceFiles(info *types.Info, fs []*ast.File) {
	for _, f := range fs {
		traceDecls(info, f.Decls)
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
		Selections: make(map[*ast.SelectorExpr]*types.Selection),
	}
	_, err = conf.Check("simpledb", fset, files, info)
	if err != nil {
		panic(err)
	}
	traceFiles(info, files)
}
