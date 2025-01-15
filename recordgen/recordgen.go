package recordgen

import (
	"fmt"
	"github.com/goose-lang/goose/glang"
	"go/ast"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/packages"
	"io"
	"log"
	"strings"
)

func (ctx *Ctx) toCoqType(t types.Type) string {
	switch t := t.(type) {
	case *types.Basic:
		switch t.Name() {
		case "uint64", "int64":
			return "w64"
		case "uint32", "int32":
			return "w32"
		case "uint8", "int8", "byte":
			return "w8"
		case "int":
			return "w64"
		case "bool":
			return "bool"
		case "string", "untyped string":
			return "go_string"
		}
	case *types.Slice:
		return "slice.t"
	case *types.Array:
		return fmt.Sprintf("(vec %s %d)", ctx.toCoqType(t.Elem()), t.Len())
	case *types.Pointer:
		return "loc"
	case *types.Signature:
		return "func.t"
	case *types.Interface:
		return "interface.t"
	case *types.Map, *types.Chan:
		return "loc"
	case *types.Named:
		u := t.Underlying()
		if _, ok := u.(*types.Struct); ok {
			if ctx.pkgPath == t.Obj().Pkg().Path() {
				return t.Obj().Name() + ".t"
			} else {
				coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(t.Obj().Pkg().Path()), "/", ".")
				if _, ok := ctx.importsSet[coqPath]; !ok {
					ctx.importsList = append(ctx.importsList, coqPath)
					ctx.importsSet[coqPath] = struct{}{}
				}
				return fmt.Sprintf("%s.%s.t", t.Obj().Pkg().Name(), t.Obj().Name())
			}
		}
		return ctx.toCoqType(u)
	}
	panic(fmt.Sprint("Unknown type", t))
}

func toCoqName(n string) string {
	if n == "Type" {
		return "Type'"
	} else if n == "t" {
		return "t'"
	}
	return n
}

type Ctx struct {
	pkgPath string

	deps        map[string][]string
	currentName string
	defs        map[string]string
	defNames    []string

	importsList []string
	importsSet  map[string]struct{}
}

func (ctx *Ctx) setCurrent(s string) {
	if ctx.currentName != "" {
		panic("recordgen: setting currentName before unsetting")
	}
	ctx.currentName = s
}

func (ctx *Ctx) unsetCurrent() {
	ctx.currentName = ""
}

func (ctx *Ctx) addDep(s string) {
	ctx.deps[ctx.currentName] = append(ctx.deps[ctx.currentName], s)
}

func (ctx *Ctx) Decl(info types.Info, d ast.Decl) {
	switch d := d.(type) {
	case *ast.FuncDecl:
	case *ast.GenDecl:
		switch d.Tok {
		case token.TYPE:
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				if s, ok := info.TypeOf(spec.Type).(*types.Struct); ok {
					name := spec.Name.Name
					w := new(strings.Builder)
					// Record type
					defName := name + ".t"
					ctx.setCurrent(defName)
					defer ctx.unsetCurrent()

					fmt.Fprintf(w, "Module %s.\nSection def.\nContext `{ffi_syntax}.\nRecord t := mk {\n", name)
					for i := 0; i < s.NumFields(); i++ {
						t := ctx.toCoqType(s.Field(i).Type())
						ctx.addDep(t)
						fmt.Fprintf(w, "  %s : %s;\n",
							toCoqName(s.Field(i).Name()),
							t,
						)
					}
					fmt.Fprintf(w, "}.\nEnd def.\nEnd %s.\n\n", name)

					// Settable instance
					if s.NumFields() > 0 {
						fmt.Fprintf(w, `
Global Instance settable_%s `+"`{ffi_syntax}"+`: Settable _ :=
  settable! %s.mk <`, name, name)
						sep := ""
						for i := 0; i < s.NumFields(); i++ {
							fmt.Fprintf(w, "%s %s.%s", sep, name, toCoqName(s.Field(i).Name()))
							sep = ";"
						}
						fmt.Fprintf(w, " >.\n")
					}

					fmt.Fprintf(w, `Global Instance into_val_%s `+"`"+`{ffi_syntax} : IntoVal %s.t.
Admitted.

`, name, name,
					)

					// IntoValTyped instance
					fmt.Fprintf(w, `Global Instance into_val_typed_%s `+"`"+`{ffi_syntax} : IntoValTyped %s.t %s :=
{|
`,
						name, name, name,
					)
					// default_val
					fmt.Fprintf(w, "  default_val := %s.mk", name)
					for i := 0; i < s.NumFields(); i++ {
						fmt.Fprintf(w, " (default_val _)")
					}
					fmt.Fprintf(w, `;
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
`)

					// IntoValStructField instances
					for i := 0; i < s.NumFields(); i++ {
						fieldName := s.Field(i).Name()
						instanceName := "into_val_struct_field_" + name + "_" + fieldName
						fmt.Fprintf(w, `Global Instance %s `+"`"+`{ffi_syntax} : IntoValStructField "%s" %s %s.%s.
Admitted.

`,
							instanceName, fieldName, name, name, toCoqName(fieldName),
						)
					}

					// PureWp instance
					fmt.Fprintf(w, "Instance wp_struct_make_%s `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}", name)
					for i := 0; i < s.NumFields(); i++ {
						fmt.Fprintf(w, " %s", toCoqName(s.Field(i).Name()))
					}
					fmt.Fprintf(w, ":\n  PureWp True\n    (struct.make %s (struct.fields_val [", name)
					sep := ""
					for i := 0; i < s.NumFields(); i++ {
						fmt.Fprintf(w, "%s\n      \"%s\" ::= #%s", sep, s.Field(i).Name(), toCoqName(s.Field(i).Name()))
						sep = ";"
					}
					fmt.Fprint(w, "\n    ]))%%V \n    #(")
					fmt.Fprintf(w, "%s.mk", name)
					for i := 0; i < s.NumFields(); i++ {
						fmt.Fprintf(w, " %s", toCoqName(s.Field(i).Name()))
					}
					fmt.Fprintf(w, ").\nAdmitted.\n\n")

					ctx.defNames = append(ctx.defNames, defName)
					ctx.defs[defName] = w.String()
				}
			}
		}
	case *ast.BadDecl:
	default:
	}
}

func Package(w io.Writer, pkg *packages.Package) {
	fmt.Fprintf(w, "(* autogenerated by goose record generator; do not modify *)\n")
	coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath), "/", ".")
	fmt.Fprintf(w, "From New.code Require Import %s.\n", coqPath)
	fmt.Fprintf(w, "From New.golang Require Import theory.\n\n")

	ctx := &Ctx{
		deps:       make(map[string][]string),
		defs:       make(map[string]string),
		importsSet: make(map[string]struct{}),
		pkgPath:    pkg.PkgPath,
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			ctx.Decl(*pkg.TypesInfo, d)
		}
	}

	// print in sorted order, printing error if there's a cycle
	for _, imp := range ctx.importsList {
		fmt.Fprintf(w, "From New.proof.structs Require %s.\n", imp)
	}
	fmt.Fprintf(w, "Axiom falso : False.\n\n") // FIXME: get rid of this
	var printingOrdered []string
	printing := make(map[string]bool)
	printed := make(map[string]bool)
	var printDefAndDeps func(string)

	printDefAndDeps = func(n string) {
		if printed[n] {
			return
		} else if printing[n] {
			log.Fatal("Found a cyclic dependency: ", printingOrdered)
		}

		printingOrdered = append(printingOrdered, n)
		printing[n] = true
		defer func() {
			printingOrdered = printingOrdered[:len(printingOrdered)-1]
			delete(printing, n)
		}()

		for _, depName := range ctx.deps[n] {
			printDefAndDeps(depName)
		}
		fmt.Fprintf(w, ctx.defs[n])
		printed[n] = true
	}
	for _, d := range ctx.defNames {
		printDefAndDeps(d)
	}
}
