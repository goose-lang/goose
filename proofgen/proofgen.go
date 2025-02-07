package proofgen

import (
	"fmt"
	"io"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"golang.org/x/tools/go/packages"
)

func Package(w func(string) io.Writer, pkg *packages.Package, usingFfi bool, ffi string, filter declfilter.DeclFilter) {
	coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath), "/", ".")
	fmt.Fprintf(w(""), "Require New.generatedproof.%s__types.\n", coqPath)
	fmt.Fprintf(w(""), "Require New.generatedproof.%s__names.\n", coqPath)
	if filter.HasTrusted() {
		fmt.Fprintf(w(""), "Require Export New.manualproof.%s.\n", coqPath)
	}
	fmt.Fprintf(w(""), "Module %s.\n", pkg.Name)
	fmt.Fprintf(w(""), "Export %s__types.\n", coqPath)
	fmt.Fprintf(w(""), "Export %s__names.\n", coqPath)
	if filter.HasTrusted() {
		fmt.Fprintf(w(""), "Export manualproof.%s.\n", coqPath)
	}
	fmt.Fprintf(w(""), "End %s.\n", pkg.Name)

	if filter.HasTrusted() {
		fmt.Fprintf(w("names"), "Require Export New.manualproof.%s.\n", coqPath)
		fmt.Fprintf(w("types"), "Require Export New.manualproof.%s.\n", coqPath)
	}

	translateTypes(w("types"), pkg, usingFfi, ffi, filter)
	translateNames(w("names"), pkg, usingFfi, ffi, filter)
}
