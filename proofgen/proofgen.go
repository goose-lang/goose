package proofgen

import (
	"golang.org/x/tools/go/packages"
	"io"
)

func Package(w io.Writer, pkg *packages.Package, usingFfi bool, ffi string) {
	translateTypes(w, pkg, usingFfi, ffi)
	translateNames(w, pkg, usingFfi, ffi)
}
