package proofgen

import (
	"fmt"
	"io"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"golang.org/x/tools/go/packages"
)

func Package(w io.Writer, pkg *packages.Package, usingFfi bool, ffi string, filter declfilter.DeclFilter) {
	if filter.HasTrusted() {
		coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath), "/", ".")
		fmt.Fprintf(w, "Require Export New.manualproof.%s.\n", coqPath)
	}
	translateTypes(w, pkg, usingFfi, ffi, filter)
	translateNames(w, pkg, usingFfi, ffi, filter)
}
