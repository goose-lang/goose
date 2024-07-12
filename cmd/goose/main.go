package main

import (
	"bytes"
	"flag"
	"fmt"
	"os"
	"path"

	"github.com/fatih/color"

	"github.com/tchajed/goose"
	"github.com/tchajed/goose/glang"
)

// write data to file name, first checking if it already has those contents
//
// like os.WriteFile, creates name if it doesn't exist and doesn't set perm if
// the file does exist
func writeFileIfChanged(name string, data []byte, perm os.FileMode) error {
	contents, err := os.ReadFile(name)
	if err != nil {
		return os.WriteFile(name, data, perm)
	}
	// file has correct contents, return
	if bytes.Compare(contents, data) == 0 {
		return nil
	}
	return os.WriteFile(name, data, perm)
}

func coqFileContents(f glang.File) []byte {
	var b bytes.Buffer
	f.Write(&b)
	return b.Bytes()
}

func translate(pkgPatterns []string, outRootDir string, modDir string,
	ignoreErrors bool, tr goose.Translator) {
	red := color.New(color.FgRed).SprintFunc()
	fs, errs, patternError := tr.TranslatePackages(modDir, pkgPatterns...)
	if patternError != nil {
		fmt.Fprintln(os.Stderr, red(patternError.Error()))
		os.Exit(1)
	}

	someError := false
	for i, f := range fs {
		err := errs[i]
		if err != nil {
			fmt.Fprintln(os.Stderr, red(err.Error()))
			someError = true
			if !ignoreErrors {
				continue
			}
		}
		outFile := path.Join(outRootDir,
			glang.ImportToPath(f.PkgPath, f.GoPackage))
		outDir := path.Dir(outFile)
		err = os.MkdirAll(outDir, 0777)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not create output directory"))
		}
		err = writeFileIfChanged(outFile, coqFileContents(f), 0666)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
	}
	if someError {
		os.Exit(1)
	}
}

// noinspection GoUnhandledErrorResult
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

	translate(flag.Args(), outRootDir, modDir, ignoreErrors, tr)
}
