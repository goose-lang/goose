package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/tchajed/goose"
)

func main() {
	var config goose.Config
	flag.BoolVar(&config.AddSourceFileComments, "source-comments", false,
		"add comments indicating Go source code location for each top-level declaration")

	flag.Parse()
	if flag.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "Usage: goose <path to source dir>")
		os.Exit(1)
	}
	srcDir := flag.Arg(0)

	f, err := config.TranslatePackage(srcDir)
	if err != nil {
		fmt.Fprintln(os.Stderr, err.Error())
		os.Exit(1)
	}
	f.Write(os.Stdout)
}
