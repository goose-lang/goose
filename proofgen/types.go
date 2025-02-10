package proofgen

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"io"
	"log"
	"strconv"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"golang.org/x/tools/go/packages"
)

type typesTranslator struct {
	pkg *packages.Package

	filter declfilter.DeclFilter

	deps        map[string][]string
	currentName string
	defs        map[string]string
	defNames    []string
}

// Adding a "'" to avoid conflicting with Coq keywords and definitions that
// would already be in context (like `t`). Could do this only when there is a
// conflict, but it's lower entropy to do it always rather than pick and
// choosing when.
func toCoqName(n string) string {
	return n + "'"
}

func (tr *typesTranslator) setCurrent(s string) {
	if tr.currentName != "" {
		panic("recordgen: setting currentName before unsetting")
	}
	tr.currentName = s
}

func (tr *typesTranslator) unsetCurrent() {
	tr.currentName = ""
}

func (tr *typesTranslator) addDep(s string) {
	tr.deps[tr.currentName] = append(tr.deps[tr.currentName], s)
}

func (tr *typesTranslator) toCoqTypeWithDeps(t types.Type, pkg *packages.Package) string {
	switch t := t.(type) {
	case *types.Basic:
		switch t.Name() {
		case "uint64", "int64":
			return "w64"
		case "uint32", "int32":
			return "w32"
		case "uint16", "int16":
			return "w16"
		case "uint8", "int8", "byte":
			return "w8"
		case "uint", "int":
			return "w64"
		case "float64":
			return "w64"
		case "bool":
			return "bool"
		case "string", "untyped string":
			return "go_string"
		case "Pointer", "uintptr":
			return "loc"
		default:
			panic(fmt.Sprintf("Unknown basic type %s", t.Name()))
		}
	case *types.Slice:
		return "slice.t"
	case *types.Array:
		return fmt.Sprintf("(vec %s %d)", tr.toCoqTypeWithDeps(t.Elem(), pkg), t.Len())
	case *types.Pointer:
		return "loc"
	case *types.Signature:
		return "func.t"
	case *types.Interface:
		return "interface.t"
	case *types.Map, *types.Chan:
		return "loc"
	case *types.Named:
		if t.Obj().Pkg() == nil || pkg.PkgPath == t.Obj().Pkg().Path() {
			n := t.Obj().Name() + ".t"
			tr.addDep(n)
			return n
		} else {
			n := fmt.Sprintf("%s.%s.t", t.Obj().Pkg().Name(), t.Obj().Name())
			tr.addDep(n)
			return n
		}
	case *types.Struct:
		if t.NumFields() == 0 {
			return "unit"
		} else {
			panic(fmt.Sprintf("Anonymous structs with fields are not supported (%s): %s",
				pkg.Fset.Position(t.Field(0).Pos()).String(),
				t.String()))
		}
	}
	panic(fmt.Sprint("Unknown type ", t))
}

func (tr *typesTranslator) axiomatizeType(spec *ast.TypeSpec) {
	name := spec.Name.Name
	defName := name + ".t"
	tr.setCurrent(defName)
	defer tr.unsetCurrent()

	w := new(strings.Builder)
	fmt.Fprintf(w, "Module %s.\nSection def.\nContext `{ffi_syntax}.\nAxiom t : Type.\nEnd def.\nEnd %s.\n",
		name, name)
	fmt.Fprintf(w, `
Global Instance into_val_%s `+"`"+`{ffi_syntax} : IntoVal %s.t.
Admitted.
`, name, name,
	)

	// IntoValTyped instance
	fmt.Fprintf(w, `
Global Instance into_val_typed_%s `+"`"+`{ffi_syntax} : IntoValTyped %s.t %s.%s.
`,
		name, name, tr.pkg.Name, name)
	fmt.Fprintf(w, "Admitted.\n")

	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = w.String()
}

func (tr *typesTranslator) translateSimpleType(spec *ast.TypeSpec, t types.Type) {
	name := spec.Name.Name
	defName := name + ".t"
	tr.setCurrent(defName)
	defer tr.unsetCurrent()

	w := new(strings.Builder)
	fmt.Fprintf(w, "\nModule %s.\nSection def.\nContext `{ffi_syntax}.\nDefinition t := %s.\nEnd def.\nEnd %s.\n",
		name, tr.toCoqTypeWithDeps(t, tr.pkg), name)

	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = w.String()
}

func (tr *typesTranslator) translateStructType(spec *ast.TypeSpec, s *types.Struct) {
	name := spec.Name.Name
	w := new(strings.Builder)
	defName := name + ".t"
	tr.setCurrent(defName)
	defer tr.unsetCurrent()

	getFieldName := func(i int) string {
		fieldName := s.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_" + strconv.Itoa(i)
		}
		return fieldName
	}

	fmt.Fprintf(w, "Module %s.\nSection def.\nContext `{ffi_syntax}.\nRecord t := mk {\n", name)
	for i := 0; i < s.NumFields(); i++ {
		t := tr.toCoqTypeWithDeps(s.Field(i).Type(), tr.pkg)
		fmt.Fprintf(w, "  %s : %s;\n",
			toCoqName(getFieldName(i)),
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
			fmt.Fprintf(w, "%s %s.%s", sep, name, toCoqName(getFieldName(i)))
			sep = ";"
		}
		fmt.Fprintf(w, " >.\n")
	}

	fmt.Fprintf(w, `Global Instance into_val_%s `+"`"+`{ffi_syntax} : IntoVal %s.t.
Admitted.

`, name, name,
	)

	// IntoValTyped instance
	fmt.Fprintf(w, `Global Instance into_val_typed_%s `+"`"+`{ffi_syntax} : IntoValTyped %s.t %s.%s :=
{|
`,
		name, name, tr.pkg.Name, name,
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
		instanceName := "into_val_struct_field_" + name + "_" + getFieldName(i)
		fmt.Fprintf(w, `Global Instance %s `+"`"+`{ffi_syntax} : IntoValStructField "%s" %s.%s %s.%s.
Admitted.

`,
			instanceName, getFieldName(i), tr.pkg.Name, name, name, toCoqName(getFieldName(i)),
		)
	}

	// PureWp instance
	fmt.Fprintf(w, "Global Instance wp_struct_make_%s `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}", name)
	for i := 0; i < s.NumFields(); i++ {
		fmt.Fprintf(w, " %s", toCoqName(getFieldName(i)))
	}
	fmt.Fprintf(w, ":\n  PureWp True\n    (struct.make %s.%s (alist_val [", tr.pkg.Name, name)
	sep := ""
	for i := 0; i < s.NumFields(); i++ {
		fmt.Fprintf(w, "%s\n      \"%s\" ::= #%s", sep, getFieldName(i), toCoqName(getFieldName(i)))
		sep = ";"
	}
	fmt.Fprint(w, "\n    ]))%%V\n    #(")
	fmt.Fprintf(w, "%s.mk", name)
	for i := 0; i < s.NumFields(); i++ {
		fmt.Fprintf(w, " %s", toCoqName(getFieldName(i)))
	}
	fmt.Fprintf(w, ").\nAdmitted.\n\n")

	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = w.String()
}

func (tr *typesTranslator) translateType(spec *ast.TypeSpec) {
	switch s := tr.pkg.TypesInfo.TypeOf(spec.Type).(type) {
	case *types.Struct:
		tr.translateStructType(spec, s)
	default:
		tr.translateSimpleType(spec, s)
		// panic(fmt.Sprintf("Unsupported type %s", s.String()))
	}
}

func (tr *typesTranslator) Decl(d ast.Decl) {
	switch d := d.(type) {
	case *ast.FuncDecl:
	case *ast.GenDecl:
		switch d.Tok {
		case token.TYPE:
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				switch tr.filter.GetAction(spec.Name.Name) {
				case declfilter.Translate:
					tr.translateType(spec)
				case declfilter.Axiomatize:
					tr.axiomatizeType(spec)
				case declfilter.Skip, declfilter.Trust:
					continue
				}
			}
		}
	case *ast.BadDecl:
	default:
	}
}

func translateTypes(w io.Writer, pkg *packages.Package, usingFfi bool, ffi string, filter declfilter.DeclFilter) {
	tr := &typesTranslator{
		deps:   make(map[string][]string),
		defs:   make(map[string]string),
		pkg:    pkg,
		filter: filter,
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}

	fmt.Fprintf(w, "Axiom falso : False.\n") // FIXME: get rid of this
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

		for _, depName := range tr.deps[n] {
			printDefAndDeps(depName)
		}
		fmt.Fprintf(w, tr.defs[n])
		printed[n] = true
	}
	for _, d := range tr.defNames {
		printDefAndDeps(d)
	}
}
