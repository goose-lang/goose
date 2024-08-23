package axiomgen

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"io"
	"log"
)

func Decl(w io.Writer, info types.Info, d ast.Decl) {
	switch d := d.(type) {
	case *ast.FuncDecl:
		if d.Name.IsExported() {
			n := d.Name.Name
			if d.Recv != nil {
				recvType := info.TypeOf(d.Recv.List[0].Type)
				if baseType, ok := recvType.(*types.Pointer); ok {
					recvType = baseType.Elem()
				}
				namedType, ok := recvType.(*types.Named)
				if !ok {
					log.Fatalf("expected named type as method receiver, got %T", recvType)
				}
				n = namedType.Obj().Name() + "__" + n
			}
			fmt.Fprintf(w, "Axiom %s : val.\n", n)
		}
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
		case token.VAR:
			// return ctx.globalVarDecl(d)
		case token.TYPE:
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				if spec.Name.IsExported() {
					fmt.Fprintf(w, "Axiom %s : go_type.\n", spec.Name.Name)
					fmt.Fprintf(w, "Axiom %s__mset : list (string * val).\n", spec.Name.Name)
					fmt.Fprintf(w, "Axiom %s__mset_ptr : list (string * val).\n", spec.Name.Name)
				}
			}
		}
	case *ast.BadDecl:
	default:
	}
}
