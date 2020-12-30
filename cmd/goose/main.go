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

//noinspection GoUnhandledErrorResult
func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: goose [options] <path to go package>")

		flag.PrintDefaults()
	}
	var config goose.Config
	flag.BoolVar(&config.AddSourceFileComments, "source-comments", false,
		"add comments indicating Go source code location for each top-level declaration")
	flag.BoolVar(&config.TypeCheck, "typecheck", false,
		"add type-checking theorems")
	flag.StringVar(&config.ImportHeader, "import-line", "",
		"FFI import line (empty string defaults to disk)")

	var outFile string
	flag.StringVar(&outFile, "out", "-",
		"file to output to (use '-' for stdout)")

	var packagePath string
	flag.StringVar(&packagePath, "package", "",
		"output to a package path")

	var ignoreErrors bool
	flag.BoolVar(&ignoreErrors, "ignore-errors", false,
		"output partial translation even if there are errors")

	flag.Parse()
	if flag.NArg() != 1 {
		flag.Usage()
		os.Exit(1)
	}
	srcDir := flag.Arg(0)

	red := color.New(color.FgRed).SprintFunc()
	f, err := config.TranslatePackage(packagePath, srcDir)
	if err != nil {
		fmt.Fprintln(os.Stderr, red(err.Error()))
		if !ignoreErrors {
			os.Exit(1)
		}
	}
	if outFile == "-" {
		f.Write(os.Stdout)
	} else {
		if packagePath != "" {
			outFile = path.Join(outFile, coq.ImportToPath(packagePath))
			outDir := path.Dir(outFile)
			_, err := os.Stat(outDir)
			if os.IsNotExist(err) {
				os.MkdirAll(outDir, 0777)
			}
		}
		out, err := os.Create(outFile)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
		defer out.Close()
		f.Write(out)
	}
	if err != nil {
		os.Exit(1)
	}
}
