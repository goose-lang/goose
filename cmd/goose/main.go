package main

import (
	"flag"
	"fmt"
	"os"
	"path"

	"github.com/fatih/color"

	"github.com/tchajed/goose"
	"github.com/tchajed/goose/internal/coq"
)

func translateOne(pkgPattern string, outRootDir string, modDir string, ignoreErrors bool, tr goose.Translator) {
	red := color.New(color.FgRed).SprintFunc()
	fs, err := tr.TranslatePackage(modDir, pkgPattern)
	if err != nil {
		fmt.Fprintln(os.Stderr, red(err.Error()))
		if !ignoreErrors {
			os.Exit(1)
		}
	}

	for _, f := range fs {
		outFile := path.Join(outRootDir,
			coq.ImportToPath(f.PkgPath, f.GoPackage))
		outDir := path.Dir(outFile)
		_, err := os.Stat(outDir)
		if os.IsNotExist(err) {
			os.MkdirAll(outDir, 0777)
		}
		out, err := os.Create(outFile)
		defer out.Close()
		f.Write(out)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
	}
	if err != nil {
		os.Exit(1)
	}
}

//noinspection GoUnhandledErrorResult
func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: goose [options] <path to go package>")

		flag.PrintDefaults()
	}
	var tr goose.Translator

	flag.BoolVar(&tr.AddSourceFileComments, "source-comments", false,
		"add comments indicating Go source code location for each top-level declaration")
	flag.BoolVar(&tr.TypeCheck, "typecheck", false, "add type-checking theorems")

	var outRootDir string
	flag.StringVar(&outRootDir, "out", ".",
		"root directory for output (default is current directory)")

	var modDir string
	flag.StringVar(&modDir, "dir", ".",
		"directory containing necessary go.mod")

	var ignoreErrors bool
	flag.BoolVar(&ignoreErrors, "ignore-errors", false,
		"output partial translation even if there are errors")

	flag.Parse()

	for i := 0; i < flag.NArg(); i++ {
		pkgPattern := flag.Arg(i)
		translateOne(pkgPattern, outRootDir, modDir, ignoreErrors, tr)
	}
}
