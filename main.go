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

func (r ErrorReporter) prefixed(prefix, msg string) {
	panic(fmt.Errorf("%s: %s", prefix, msg))
}

// Docs reports a situation that I thought was impossible from reading the documentation.
func (r ErrorReporter) Docs(msg string) {
	r.prefixed("impossible(docs)", msg)
}

// NoExample reports a situation I thought was impossible because I couldn't
// think of how to do it in Go.
func (r ErrorReporter) NoExample(msg string) {
	r.prefixed("impossible(no-examples)", msg)
}

// FutureWork reports something we could theoretically handle but probably
// won't.
func (r ErrorReporter) FutureWork(msg string) {
	r.prefixed("future", msg)
}

// Todo reports a situation that is intended to be handled but we haven't gotten
// around to.
func (r ErrorReporter) Todo(msg string) {
	r.prefixed("todo", msg)
}

// Unhandled reports something intentionally unhandled (the code should not use
// this feature).
func (r ErrorReporter) Unhandled(msg string) {
	r.prefixed("unhandled", msg)
}

var error ErrorReporter

func traceDecls(ds []ast.Decl) {
	for _, d := range ds {
		switch v := d.(type) {
		case *ast.FuncDecl:
			spew.Printf("func %s\n%#v\n", v.Name.Name, v)
		case *ast.GenDecl:
			switch v.Tok {
			case token.IMPORT, token.CONST, token.VAR:
				continue
			case token.TYPE:
				if len(v.Specs) > 1 {
					error.NoExample("multiple specs in a type decl")
				}
				s := v.Specs[0].(*ast.TypeSpec)
				spew.Printf("type %s\n%#v\n", s.Name.Name, s)
			default:
				error.Docs("unknown gendecl token type")
			}
		default:
			error.NoExample("top-level decl")
		}
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
