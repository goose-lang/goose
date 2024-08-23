package axiomgen

import (
	"fmt"
	"go/ast"
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
	case *ast.BadDecl:
	default:
	}

}
