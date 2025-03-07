package proofgen

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"io"

	"github.com/goose-lang/goose/declfilter"
	"golang.org/x/tools/go/packages"
)

type namesTranslator struct {
	pkg *packages.Package

	filter declfilter.DeclFilter

	varNames    []string
	varCoqTypes []string
	functions   []string
	namedTypes  []*types.Named

	usingFfi bool
	ffi      string
}

func (tr *namesTranslator) Decl(d ast.Decl) {
	info := tr.pkg.TypesInfo
	switch d := d.(type) {
	case *ast.GenDecl:
		switch d.Tok {
		case token.VAR:
			for _, spec := range d.Specs {
				s := spec.(*ast.ValueSpec)
				for _, name := range s.Names {
					if name.Name != "_" && tr.filter.GetAction(name.Name) == declfilter.Translate {
						tr.varNames = append(tr.varNames, name.Name)
						tr.varCoqTypes = append(tr.varCoqTypes,
							toCoqType(info.TypeOf(name), tr.pkg))
					}
				}
			}
		case token.TYPE:
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				if t, ok := info.TypeOf(spec.Name).(*types.Named); ok {
					if _, ok := t.Underlying().(*types.Interface); !ok {
						tr.namedTypes = append(tr.namedTypes, t)
					}
				}
			}
		}
	case *ast.FuncDecl:
		if d.Recv == nil && d.Name.Name != "init" && d.Name.Name != "_" {
			tr.functions = append(tr.functions, d.Name.Name)
		}
	case *ast.BadDecl:
	default:
	}
}

func translateNames(w io.Writer, pkg *packages.Package, usingFfi bool, ffi string, filter declfilter.DeclFilter) {
	tr := &namesTranslator{pkg: pkg, filter: filter}

	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}

	fmt.Fprintf(w, "\nSection names.\n")
	// emit record for global addrs
	fmt.Fprintf(w, `
Class GlobalAddrs :=
{
`)
	for _, varName := range tr.varNames {
		fmt.Fprintf(w, "  %s : loc;\n", varName)
	}
	fmt.Fprint(w, "}.\n\n")
	fmt.Fprint(w, "Context `{!GlobalAddrs}.\n")
	if !usingFfi {
		fmt.Fprint(w, "Context `{hG: heapGS Σ, !ffi_semantics _ _}.\n")
	} else {
		fmt.Fprint(w, "Context `{!heapGS Σ}.\n")
	}
	fmt.Fprint(w, "Context `{!goGlobalsGS Σ}.\n\n")

	// emit `var_addrs` which converts GlobalAddrs into alist
	fmt.Fprint(w, "Definition var_addrs : list (go_string * loc) := [")
	sep := ""
	for _, varName := range tr.varNames {
		fmt.Fprintf(w, "%s\n    (\"%s\"%%go, %s)", sep, varName, varName)
		sep = ";"
	}
	fmt.Fprintln(w, "\n  ].")

	// emit `PkgIsDefined instance`
	fmt.Fprintf(w, `
Global Instance is_pkg_defined_instance : IsPkgDefined %s :=
{|
  is_pkg_defined := is_global_definitions %s var_addrs;
|}.
`, pkg.Name, pkg.Name)

	// emit `own_allocated`
	fmt.Fprint(w, "\nDefinition own_allocated `{!GlobalAddrs} : iProp Σ :=\n")
	if len(tr.varNames) == 0 {
		fmt.Fprintf(w, "True.\n")
	} else {
		for i, varName := range tr.varNames {
			sep := "."
			if i < len(tr.varNames)-1 {
				sep = " ∗"
			}
			varType := tr.varCoqTypes[i]
			fmt.Fprintf(w, `  "H%s" ∷ %s ↦ (default_val %s)%s
`,
				varName, varName, varType, sep)
		}
	}

	// emit instances for global.get
	for _, varName := range tr.varNames {
		fmt.Fprintf(w, "\nGlobal Instance wp_globals_get_%s : \n", varName)
		fmt.Fprintf(w, "  WpGlobalsGet %s \"%s\" %s (is_pkg_defined %s).\n", pkg.Name, varName, varName, pkg.Name)
		fmt.Fprintf(w, "Proof. apply wp_globals_get'. reflexivity. Qed.\n")
	}

	// emit instances for unfolding func_call
	for _, funcName := range tr.functions {
		if tr.filter.GetAction(funcName) == declfilter.Skip {
			continue
		}
		fmt.Fprintf(w, "\nGlobal Instance wp_func_call_%s :\n", funcName)
		fmt.Fprintf(w, "  WpFuncCall %s \"%s\" _ (is_pkg_defined %s) :=\n", pkg.Name, funcName, pkg.Name)
		fmt.Fprintf(w, "  ltac:(apply wp_func_call'; reflexivity).\n")
	}

	// emit instances for unfolding method_call
	for _, namedType := range tr.namedTypes {
		baseTypeName := namedType.Obj().Name()
		typeName := namedType.Obj().Name()
		goMset := types.NewMethodSet(namedType)
		for i := range goMset.Len() {
			methodName := goMset.At(i).Obj().Name()
			if tr.filter.GetAction(baseTypeName+"."+methodName) == declfilter.Skip {
				continue
			}

			fmt.Fprintf(w, "\nGlobal Instance wp_method_call_%s_%s :\n", typeName, methodName)
			fmt.Fprintf(w, "  WpMethodCall %s \"%s\" \"%s\" _ (is_pkg_defined %s) :=\n",
				pkg.Name, typeName, methodName, pkg.Name)
			fmt.Fprintf(w, "  ltac:(apply wp_method_call'; reflexivity).\n")
			// XXX: by using an ltac expression to generate the instance, we can
			// leave an evar for the method val, avoiding the need to write out
			// the promoted methods.
		}

		typeName = namedType.Obj().Name() + "'ptr"
		goMset = types.NewMethodSet(types.NewPointer(namedType))
		for i := range goMset.Len() {
			methodName := goMset.At(i).Obj().Name()
			if tr.filter.GetAction(baseTypeName+"."+methodName) == declfilter.Skip {
				continue
			}

			fmt.Fprintf(w, "\nGlobal Instance wp_method_call_%s_%s :\n", typeName, methodName)
			fmt.Fprintf(w, "  WpMethodCall %s \"%s\" \"%s\" _ (is_pkg_defined %s) :=\n",
				pkg.Name, typeName, methodName, pkg.Name)
			fmt.Fprintf(w, "  ltac:(apply wp_method_call'; reflexivity).\n")
		}
	}

	fmt.Fprintf(w, "\nEnd names.\n")
}
