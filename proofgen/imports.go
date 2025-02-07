package proofgen

import (
	"fmt"
	"go/ast"
	"go/token"
	"io"
	"strconv"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"golang.org/x/tools/go/packages"
)

type importsTranslator struct {
	importsList []string
	importsSet  map[string]struct{}

	filter declfilter.DeclFilter
}

func (tr *importsTranslator) Decl(d ast.Decl) {
	switch d := d.(type) {
	case *ast.GenDecl:
		switch d.Tok {
		case token.IMPORT:
			for _, spec := range d.Specs {
				spec := spec.(*ast.ImportSpec)
				importPath, _ := strconv.Unquote(spec.Path.Value)
				if tr.filter.ShouldImport(importPath) {
					coqImport := strings.ReplaceAll(
						glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(
							importPath), "/", ".")
					if _, ok := tr.importsSet[coqImport]; !ok {
						tr.importsList = append(tr.importsList, coqImport)
						tr.importsSet[coqImport] = struct{}{}
					}
				}
			}
		}
	}
}

func translateImports(w io.Writer, pkg *packages.Package, usingFfi bool, ffi string, filter declfilter.DeclFilter) {
	tr := &importsTranslator{
		importsSet: make(map[string]struct{}),
		filter:     filter,
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}
	for _, imp := range tr.importsList {
		fmt.Fprintf(w, "Require Export New.generatedproof.%s.\n", imp)
	}
}
