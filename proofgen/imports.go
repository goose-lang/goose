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

func translateImports(pkg *packages.Package, filter declfilter.DeclFilter) (imports []tmpl.Import) {
	importsSeen := make(map[string]bool)
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			switch d := d.(type) {
			case *ast.GenDecl:
				switch d.Tok {
				case token.IMPORT:
					for _, spec := range d.Specs {
						spec := spec.(*ast.ImportSpec)
						importPath, _ := strconv.Unquote(spec.Path.Value)
						if !filter.ShouldImport(importPath) {
							continue
						}
						coqImport := strings.ReplaceAll(
							glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(
								importPath), "/", ".")
						if importsSeen[coqImport] {
							continue
						}
						imports = append(imports, tmpl.Import{Path: coqImport})
						importsSeen[coqImport] = true
					}
				}
			}
		}
	}
	return
}
