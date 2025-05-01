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

	imp := translateImports(io.Discard, pkg, usingFfi, ffi, filter)
	for _, i := range imp.importsList {
		pf.Imports = append(pf.Imports, tmpl.Import{
			Path: i,
		})
	}

	var typesOut bytes.Buffer
	translateTypes(&typesOut, pkg, usingFfi, ffi, filter)
	pf.TypesCode = typesOut.String()

	var namesOut bytes.Buffer
	translateNames(&namesOut, pkg, usingFfi, ffi, filter)
	pf.NamesCode = namesOut.String()

	if err := pf.Write(w); err != nil {
		panic(err)
	}
}
