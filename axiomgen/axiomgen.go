package axiomgen

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"io"
)

func Decl(w io.Writer, info types.Info, d ast.Decl) {
	switch d := d.(type) {
	case *ast.GenDecl:
		switch d.Tok {
		case token.IMPORT:
		case token.CONST:
			for _, spec := range d.Specs {
				spec := spec.(*ast.ValueSpec)
				for _, name := range spec.Names {
					if name.IsExported() {
						t := "expr"
						if basicType, ok := info.TypeOf(name).(*types.Basic); ok {
							switch basicType.Kind() {
							case types.UntypedString:
								t = "string"
							case types.UntypedInt:
								t = "Z"
							}
						}
						fmt.Fprintf(w, "Axiom %s : %s.\n", name.Name, t)
					}
				}
			}
		case token.TYPE:
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				if spec.Name.IsExported() {
					fmt.Fprintf(w, "Axiom %s : go_type.\n", spec.Name.Name)
				}
			}
		}
	case *ast.BadDecl:
	default:
	}
}

func InitializeDecl(w io.Writer, pkgPath string) {
	fmt.Fprintf(w, "Definition pkg_name' : go_string := \"%s\".\n", pkgPath)
	fmt.Fprintf(w, "Axiom initialize' : val.\n")
}
