package main

import (
	"flag"
	"fmt"
	"github.com/goose-lang/goose/proofgen"
	"github.com/goose-lang/goose/util"
)

func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: proofgen [options] <path to go package>")
		flag.PrintDefaults()
	}

	var outRootDir string
	flag.StringVar(&outRootDir, "out", ".",
		"root directory for output (default is current directory)")

	var modDir string
	flag.StringVar(&modDir, "dir", ".",
		"directory containing necessary go.mod")

	flag.Parse()

	util.Translate(proofgen.Package, flag.Args(), outRootDir, modDir)
}
