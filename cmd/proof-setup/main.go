package main

import (
	"flag"
	"fmt"

	"github.com/fatih/color"
	"github.com/goose-lang/goose/proofsetup"
	"github.com/goose-lang/goose/util"
	"golang.org/x/tools/go/packages"
)

func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: proof-setup [options] <package patterns>")

		flag.PrintDefaults()
	}

	var modDir string
	flag.StringVar(&modDir, "dir", ".",
		"directory containing necessary go.mod")

	flag.Parse()
	pkgPatterns := flag.Args()

	pkgs, err := packages.Load(util.NewPackageConfig(modDir, false), pkgPatterns...)
	if err != nil {
		panic(err)
	} else if len(pkgs) == 0 {
		panic("patterns matched no packages")
	}

	blue := color.New(color.FgBlue).SprintfFunc()

	for _, pkg := range pkgs {
		pf := proofsetup.New(pkg)
		fmt.Printf("%s:\n", blue(pf.ProofPath))
		fmt.Printf(pf.SkeletonFile())
	}
}
