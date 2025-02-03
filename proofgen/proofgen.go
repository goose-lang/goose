package proofgen

import (
	"io"

	"github.com/goose-lang/goose/declfilter"
	"golang.org/x/tools/go/packages"
)

func Package(w io.Writer, pkg *packages.Package, usingFfi bool, ffi string, filter declfilter.DeclFilter) {
	translateTypes(w, pkg, usingFfi, ffi, filter)
	translateNames(w, pkg, usingFfi, ffi, filter)
}
