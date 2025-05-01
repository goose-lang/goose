package proofgen

import (
	"bytes"
	"io"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/proofgen/tmpl"
	"golang.org/x/tools/go/packages"
)

func Package(w io.Writer, pkg *packages.Package, usingFfi bool, ffi string, filter declfilter.DeclFilter) {
	if !usingFfi {
		// TODO: usingFfi should be redundant, doesn't !usingFfi imply ffi == ""?
		ffi = ""
	}
	coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath), "/", ".")

	pf := tmpl.PackageProof{
		Ffi:        ffi,
		Name:       pkg.Name,
		HasTrusted: filter.HasTrusted(),
		ImportPath: coqPath,
	}

	pf.Imports = translateImports(pkg, usingFfi, ffi, filter)

	var typesOut bytes.Buffer
	translateTypes(&typesOut, pkg, usingFfi, ffi, filter)
	pf.TypesCode = typesOut.String()

	pf.Names = translateNames(pkg, filter)

	if err := pf.Write(w); err != nil {
		panic(err)
	}
}
