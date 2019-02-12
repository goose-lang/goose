package main

import (
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"

	"github.com/davecgh/go-spew/spew"

	"github.com/tchajed/goose"
	"github.com/tchajed/goose/coq"
)

func debugDecl(fset *token.FileSet, debugIdent string, decl ast.Decl) {
	switch d := decl.(type) {
	case *ast.FuncDecl:
		if d.Name.Name == debugIdent {
			spew.Dump(d)
		}
	case *ast.GenDecl:
		if d.Tok == token.TYPE {
			if spec, ok := d.Specs[0].(*ast.TypeSpec); ok {
				if spec.Name.Name == debugIdent {
					spew.Dump(spec)
				}
			}
		}
	}
}

func main() {
	var config goose.Config
	flag.BoolVar(&config.AddSourceFileComments, "source-comments", false,
		"add comments indicating Go source code location for each top-level declaration")

	var debugIdent string
	flag.StringVar(&debugIdent, "debug", "",
		"spew an identifier (use * to spew everything)")

	flag.Parse()
	if flag.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "Usage: goose <path to source dir>")
		os.Exit(1)
	}
	srcDir := flag.Arg(0)

	fset := token.NewFileSet()
	filter := func(os.FileInfo) bool { return true }
	packages, err := parser.ParseDir(fset, srcDir, filter, parser.ParseComments)
	if err != nil {
		panic(err)
	}

	if len(packages) > 1 {
		fmt.Fprintln(os.Stderr, "can't handle files for multiple packages")
		os.Exit(1)
	}

	var pkgName string
	var files []*ast.File
	for pName, p := range packages {
		for _, f := range p.Files {
			files = append(files, f)
		}
		pkgName = pName
	}

	ctx := goose.NewCtx(fset, config)
	err = ctx.TypeCheck(pkgName, files)
	if err != nil {
		panic(err)
	}
	if debugIdent != "" {
		if debugIdent == "*" {
			spew.Dump(files)
		} else {
			for _, f := range files {
				for _, d := range f.Decls {
					debugDecl(fset, debugIdent, d)
				}
			}
		}
	}
	var decls []coq.Decl
	for _, f := range files {
		decls = append(decls, ctx.FileDecls(f)...)
	}
	fmt.Println(coq.ImportHeader)
	fmt.Println()
	for _, d := range decls {
		fmt.Println(d.CoqDecl())
		fmt.Println()
	}
}
