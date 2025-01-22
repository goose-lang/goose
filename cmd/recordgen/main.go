package main

import (
	"flag"
	"fmt"
	"github.com/goose-lang/goose/recordgen"
	"github.com/goose-lang/goose/util"
)

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

	util.Translate(recordgen.Package, flag.Args(), outRootDir, modDir, true)
}
