package main

import (
	"flag"
	"go/parser"
	"go/token"
	"os"

	"github.com/davecgh/go-spew/spew"
)

func main() {
	flag.Parse()
	if flag.NArg() < 1 {
		panic("Usage: goose <package name>")
	}
	packageName := flag.Arg(0)

	fset := token.NewFileSet()
	filter := func(os.FileInfo) bool { return true }
	packages, err := parser.ParseDir(fset, ".", filter, parser.Mode(0))
	if err != nil {
		panic(err)
	}
	spew.Dump(packages[packageName])
}
