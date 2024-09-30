package main

import (
	"bytes"
	"flag"
	"fmt"
	"os"
	"path"
	"strings"

	"github.com/fatih/color"

	"github.com/goose-lang/goose"
	"github.com/goose-lang/goose/glang"
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
	ignoreErrors bool, namesToTranslate map[string]bool) {
	red := color.New(color.FgRed).SprintFunc()
	fs, errs, patternError := goose.TranslatePackages(modDir, namesToTranslate, pkgPatterns...)
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
	if someError && !ignoreErrors {
		os.Exit(1)
	}
}

// noinspection GoUnhandledErrorResult
func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: goose [options] <path to go package>")

		flag.PrintDefaults()
	}

	var outRootDir string
	flag.StringVar(&outRootDir, "out", ".",
		"root directory for output (default is current directory)")

	var modDir string
	flag.StringVar(&modDir, "dir", ".",
		"directory containing necessary go.mod")

	var ignoreErrors bool
	flag.BoolVar(&ignoreErrors, "ignore-errors", false,
		"output partial translation even if there are errors")

	var namesToTranslateString string
	flag.StringVar(&namesToTranslateString, "partial", "",
		"comma-separated list of Gallina identifiers to translate (if empty, translate everything)")

	flag.Parse()

	var namesToTranslate map[string]bool
	if namesToTranslateString != "" {
		namesToTranslate = make(map[string]bool)
		for _, n := range strings.Split(namesToTranslateString, ",") {
			namesToTranslate[n] = true
		}
	}

	translate(flag.Args(), outRootDir, modDir, ignoreErrors, namesToTranslate)
}
