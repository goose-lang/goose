package proofgen

import (
	"io"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/proofgen/tmpl"
	"golang.org/x/tools/go/packages"
)

func Package(w io.Writer, pkg *packages.Package, ffi string, filter declfilter.DeclFilter) {
	coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath), "/", ".")

	pf := tmpl.PackageProof{
		Ffi:        ffi,
		Name:       pkg.Name,
		HasTrusted: filter.HasTrusted(),
		ImportPath: coqPath,
	}

	pf.Imports = translateImports(pkg, filter)
	pf.Types = translateTypes(pkg, filter)
	pf.Names = translateNames(pkg, filter)

	if err := pf.Write(w); err != nil {
		panic(err)
	}
}
