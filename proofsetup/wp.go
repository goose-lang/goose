package proofsetup

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/types"
	"strings"

	"github.com/goose-lang/goose/proofgen"
	"github.com/pkg/errors"
	"golang.org/x/tools/go/packages"
)

type receiverType struct {
	Name    string
	Pointer bool
}

func (rt receiverType) FullName() string {
	if rt.Pointer {
		return rt.Name + "'ptr"
	} else {
		return rt.Name
	}
}

// getReceiverType extracts information about the receiver of a method
func getReceiverType(t types.Type) receiverType {
	switch t := types.Unalias(t).(type) {
	case *types.Named:
		return receiverType{
			Name:    t.Obj().Name(),
			Pointer: false,
		}
	case *types.Pointer:
		underlyingT := types.Unalias(t.Elem()).(*types.Named)
		return receiverType{
			Name:    underlyingT.Obj().Name(),
			Pointer: true,
		}
	}
	panic(errors.Errorf("unexpected receiver type %v", t))
}

func argGallinaBinder(pkg *packages.Package, x *ast.Ident) string {
	ty := proofgen.ToCoqType(pkg.TypesInfo.TypeOf(x), pkg)
	return fmt.Sprintf("(%s: %s)", x.Name, ty)
}

func funcDeclToWp(pkg *packages.Package, decl *ast.FuncDecl) string {
	s := new(bytes.Buffer)

	var rt *receiverType = nil
	if decl.Recv != nil {
		recv := decl.Recv.List[0].Names[0]
		t := pkg.TypesInfo.TypeOf(recv)
		actualRt := getReceiverType(t)
		rt = &actualRt
	}

	var gallinaBinders []string
	var args []string
	// TODO: binder for rt
	if rt != nil {
		recv := decl.Recv.List[0].Names[0]
		gallinaBinders = append(gallinaBinders, argGallinaBinder(pkg, recv))
	}
	for _, param := range decl.Type.Params.List {
		for _, arg := range param.Names {
			args = append(args, fmt.Sprintf("#%s", arg.Name))
			gallinaBinders = append(gallinaBinders, argGallinaBinder(pkg, arg))
		}
	}
	if len(args) == 0 {
		args = []string{"#()"}
	}

	if decl.Type.TypeParams != nil {
		var args []string
		for _, param := range decl.Type.TypeParams.List {
			for _, name := range param.Names {
				args = append(args, name.Name)
			}
		}
		fmt.Fprintf(s, "(* generic arguments %s not handled *)\n", strings.Join(args, " "))
	}
	if rt != nil {
		fmt.Fprintf(s, "Lemma wp_%s__%s %s :\n", rt.Name, decl.Name, strings.Join(gallinaBinders, " "))
	} else {
		fmt.Fprintf(s, "Lemma wp_%s %s :\n", decl.Name, strings.Join(gallinaBinders, " "))
	}

	fmt.Fprintf(s, "  {{{ is_pkg_init %s }}}\n", pkg.Name)

	if rt == nil {
		fmt.Fprintf(s, "    %s @ \"%s\" %s\n", pkg.Name, decl.Name, strings.Join(args, " "))
	} else {
		recv := decl.Recv.List[0].Names[0]
		fmt.Fprintf(s, "    %s @ %s @ \"%s\" @ \"%s\" %s\n", recv.Name, pkg.Name, rt.FullName(), decl.Name, strings.Join(args, " "))
	}

	fmt.Fprintf(s, "  {{{ RET #(); True }}}.")
	return s.String()
}

func packageWps(pkg *packages.Package) []string {
	var wps []string
	for _, f := range pkg.Syntax {
		for _, decl := range f.Decls {
			if decl, ok := decl.(*ast.FuncDecl); ok {
				wps = append(wps, funcDeclToWp(pkg, decl))
			}
		}
	}
	return wps
}
