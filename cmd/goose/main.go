package main

import (
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"

	"github.com/tchajed/goose"
	"github.com/tchajed/goose/coq"
)

func main() {
	var config goose.Config
	flag.BoolVar(&config.AddSourceFileComments, "source-comments", false,
		"add comments indicating Go source code location for each top-level declaration")

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
		fmt.Fprintln(os.Stderr, "error while parsing code:")
		fmt.Fprintln(os.Stderr, err.Error())
		os.Exit(2)
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
		fmt.Fprintln(os.Stderr, "error while type-checking code:")
		fmt.Fprintln(os.Stderr, err.Error())
		os.Exit(2)
	}

	decls, err := ctx.Decls(files...)
	if err != nil {
		fmt.Fprintln(os.Stderr, err.Error())
		os.Exit(1)
	}
	fmt.Println(coq.ImportHeader)
	fmt.Println()
	for i, d := range decls {
		fmt.Println(d.CoqDecl())
		if i != len(decls)-1 {
			fmt.Println()
		}
	}
}
