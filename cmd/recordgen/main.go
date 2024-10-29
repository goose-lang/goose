package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/token"
	"os"
	"path"
	"strings"

	"github.com/fatih/color"
	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/recordgen"
	"golang.org/x/tools/go/packages"
)

func newPackageConfig(modDir string) *packages.Config {
	mode := packages.NeedName | packages.NeedCompiledGoFiles
	mode |= packages.NeedImports
	mode |= packages.NeedTypes | packages.NeedSyntax | packages.NeedTypesInfo
	return &packages.Config{
		Dir:  modDir,
		Mode: mode,
		Fset: token.NewFileSet(),
	}
}

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

func translate(pkgPatterns []string, outRootDir string, modDir string) {
	red := color.New(color.FgRed).SprintFunc()
	pkgs, err := packages.Load(newPackageConfig(modDir), pkgPatterns...)
	if err != nil {
		panic(err)
	} else if len(pkgs) == 0 {
		panic("patterns matched no packages")
	}
	for _, pkg := range pkgs {
		w := new(strings.Builder)

		recordgen.Package(w, pkg)

		outFile := path.Join(outRootDir, glang.ImportToPath(pkg.PkgPath, pkg.Name))
		outDir := path.Dir(outFile)
		err = os.MkdirAll(outDir, 0777)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not create output directory"))
		}
		err = writeFileIfChanged(outFile, []byte(w.String()), 0666)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
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

	flag.Parse()

	translate(flag.Args(), outRootDir, modDir)
}
