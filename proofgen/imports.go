package proofgen

import (
	"go/ast"
	"go/token"
	"strconv"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/proofgen/tmpl"
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

func translateImports(pkg *packages.Package, filter declfilter.DeclFilter) []tmpl.Import {
	tr := &importsTranslator{
		importsSet: make(map[string]struct{}),
		filter:     filter,
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}
	var imports []tmpl.Import
	for _, i := range tr.importsList {
		imports = append(imports, tmpl.Import{
			Path: i,
		})
	}
	return imports
}
