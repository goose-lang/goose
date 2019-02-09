package main

import (
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"

	"github.com/davecgh/go-spew/spew"
)

// ErrorReporter groups methods for reporting errors, documenting what kind of
// issue was encountered in a uniform way.
type ErrorReporter struct{}

func (r ErrorReporter) prefixed(prefix, msg string, args ...interface{}) {
	formatted := fmt.Sprintf(msg, args...)
	panic(fmt.Errorf("%s: %s", prefix, formatted))
}

// Docs reports a situation that I thought was impossible from reading the documentation.
func (r ErrorReporter) Docs(msg string, args ...interface{}) {
	r.prefixed("impossible(docs)", msg, args...)
}

// NoExample reports a situation I thought was impossible because I couldn't
// think of how to do it in Go.
func (r ErrorReporter) NoExample(msg string, args ...interface{}) {
	r.prefixed("impossible(no-examples)", msg, args...)
}

// FutureWork reports something we could theoretically handle but probably
// won't.
func (r ErrorReporter) FutureWork(msg string, args ...interface{}) {
	r.prefixed("future", msg, args...)
}

// Todo reports a situation that is intended to be handled but we haven't gotten
// around to.
func (r ErrorReporter) Todo(msg string, args ...interface{}) {
	r.prefixed("todo", msg, args...)
}

// Unhandled reports something intentionally unhandled (the code should not use
// this feature).
func (r ErrorReporter) Unhandled(msg string, args ...interface{}) {
	r.prefixed("unhandled", msg, args...)
}

var error ErrorReporter

// TypeDecl is a name:type declaration (for a struct)
type TypeDecl struct {
	Name string
	Type string
}

// StructType is a Coq record for a Go struct
type StructType struct {
	Name   string
	Fields []TypeDecl
}

func isIdent(e ast.Expr, s string) bool {
	switch e := e.(type) {
	case *ast.Ident:
		return e.Name == s
	default:
		return false
	}
}

func mapType(e *ast.MapType) string {
	switch k := e.Key.(type) {
	case *ast.Ident:
		if k.Name == "uint64" {
			return fmt.Sprintf("HashTable(%s)", typeToString(e.Value))
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

func typeToString(e ast.Expr) string {
	switch e := e.(type) {
	case *ast.Ident:
		return e.Name
	case *ast.MapType:
		return mapType(e)
	case *ast.SelectorExpr:
		return selectorExprType(e)
	default:
	}
	error.NoExample("unexpected type expr %s", spew.Sdump(e))
	return "<type>"
}

func structDecl(name string, structTy *ast.StructType) StructType {
	ty := StructType{Name: name}
	for _, f := range structTy.Fields.List {
		if len(f.Names) > 1 {
			error.FutureWork("multiple fields for same type (split them up)")
		}
		fieldDecl := TypeDecl{
			Name: f.Names[0].Name,
			Type: typeToString(f.Type),
		}
		ty.Fields = append(ty.Fields, fieldDecl)
	}
	return ty
}

func traceDecls(ds []ast.Decl) {
	for _, d := range ds {
		switch d := d.(type) {
		case *ast.FuncDecl:
			spew.Printf("func %s\n%#v", d.Name.Name, d)
		case *ast.GenDecl:
			switch d.Tok {
			case token.IMPORT, token.CONST, token.VAR:
				continue
			case token.TYPE:
				if len(d.Specs) > 1 {
					error.NoExample("multiple specs in a type decl")
				}
				spec := d.Specs[0].(*ast.TypeSpec)
				if structTy, ok := spec.Type.(*ast.StructType); ok {
					ty := structDecl(spec.Name.Name, structTy)
					spew.Printf("type %s\n%#v\n", spec.Name.Name, structTy)
					fmt.Printf("%+v\n", ty)
				} else {
					error.Unhandled("non-struct type %s", spec.Name.Name)
				}
			default:
				error.Docs("unknown gendecl token type for %+v", d)
			}
		default:
			error.NoExample("top-level decl %s", spew.Sdump(d))
		}
		fmt.Printf("\n\n")
	}
}

func tracePackage(p *ast.Package) {
	var decls []ast.Decl
	for _, f := range p.Files {
		for _, decl := range f.Decls {
			decls = append(decls, decl)
		}
	}
	traceDecls(decls)
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
	if err != nil {
		panic(err)
	}
	p := packages[packageName]
	if p == nil {
		panic(fmt.Errorf("%s: unknown package", packageName))
	}
	tracePackage(p)
}
