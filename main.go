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

	"github.com/tchajed/goose/coq"
)

func main() {
	var config coq.Config
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

	conf := types.Config{Importer: importer.Default()}
	info := &types.Info{
		Defs:       make(map[*ast.Ident]types.Object),
		Uses:       make(map[*ast.Ident]types.Object),
		Types:      make(map[ast.Expr]types.TypeAndValue),
		Selections: make(map[*ast.SelectorExpr]*types.Selection),
	}
	_, err = conf.Check(pkgName, fset, files, info)
	if err != nil {
		panic(err)
	}
	ctx := coq.NewCtx(info, fset, config)
    decls := ctx.FileDecls(files)
	fmt.Println("From RecoveryRefinement Require Import Database.CodeSetup.")
	fmt.Println()
	for _, d := range decls {
		fmt.Println(d.CoqDecl())
		fmt.Println()
	}
}
