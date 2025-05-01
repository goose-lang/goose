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
	"github.com/goose-lang/goose/deptracker"
	"golang.org/x/tools/go/packages"
)

type typesTranslator struct {
	pkg *packages.Package

	filter declfilter.DeclFilter

	deps *deptracker.Deps
	defs map[string]string
	// tracks the order definitions were seen in
	defNames []string
}

// Adding a "'" to avoid conflicting with Coq keywords and definitions that
// would already be in context (like `t`). Could do this only when there is a
// conflict, but it's lower entropy to do it always rather than pick and
// choosing when.
func toCoqName(n string) string {
	return n + "'"
}

func (tr *typesTranslator) toCoqTypeWithDeps(t types.Type) string {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		return basicTypeToCoq(t)
	case *types.Slice:
		return "slice.t"
	case *types.Array:
		return fmt.Sprintf("(vec %s (uint.nat (W64 %d)))", tr.toCoqTypeWithDeps(t.Elem()), t.Len())
	case *types.Pointer:
		return "loc"
	case *types.Signature:
		return "func.t"
	case *types.Interface:
		return "interface.t"
	case *types.Map, *types.Chan:
		return "loc"
	case *types.Named:
		n := namedTypeToCoq(t, tr.pkg)
		tr.deps.Add(n)
		return n
	case *types.Struct:
		if t.NumFields() == 0 {
			return "unit"
		} else {
			panic(fmt.Sprintf("Anonymous structs with fields are not supported (%s): %s",
				tr.pkg.Fset.Position(t.Field(0).Pos()).String(),
				t.String()))
		}
	}
	panic(fmt.Sprintf("Unknown type %v (of type %T)", t, t))
}

func (tr *typesTranslator) axiomatizeType(spec *ast.TypeSpec) {
	name := spec.Name.Name
	defName := name + ".t"
	tr.deps.SetCurrentName(defName)
	defer tr.deps.UnsetCurrentName()

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
	tr.deps.SetCurrentName(defName)
	defer tr.deps.UnsetCurrentName()

	w := new(strings.Builder)
	fmt.Fprintf(w, "\nModule %s.\nSection def.\nContext `{ffi_syntax}.\nDefinition t := %s.\nEnd def.\nEnd %s.\n",
		name, tr.toCoqTypeWithDeps(t), name)

	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = w.String()
}

func (tr *typesTranslator) translateStructType(spec *ast.TypeSpec, s *types.Struct) {
	name := spec.Name.Name
	w := new(strings.Builder)
	defName := name + ".t"
	tr.deps.SetCurrentName(defName)
	defer tr.deps.UnsetCurrentName()

	getFieldName := func(i int) string {
		fieldName := s.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_" + strconv.Itoa(i)
		}
		return fieldName
	}

	fmt.Fprintf(w, "Module %s.\nSection def.\nContext `{ffi_syntax}.\nRecord t := mk {\n", name)
	for i := 0; i < s.NumFields(); i++ {
		t := tr.toCoqTypeWithDeps(s.Field(i).Type())
		fmt.Fprintf(w, "  %s : %s;\n",
			toCoqName(getFieldName(i)),
			t,
		)
	}
	fmt.Fprintf(w, "}.\nEnd def.\nEnd %s.\n", name)

	fmt.Fprint(w, `
Section instances.
Context `+"`"+`{ffi_syntax}.
`)

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

	fmt.Fprint(w, `
Context `+"`"+`{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
`)

	// PureWp instance
	fmt.Fprintf(w, "Global Instance wp_struct_make_%s `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}", name)
	for i := 0; i < s.NumFields(); i++ {
		fmt.Fprintf(w, " %s", toCoqName(getFieldName(i)))
	}
	// NOTE: this constructs a GolangTypeExpr
	typeExpr := fmt.Sprintf("#%s.%s", tr.pkg.Name, name)
	fmt.Fprintf(w, ":\n  PureWp True\n    (struct.make %s (alist_val [", typeExpr)
	sep := ""
	for i := 0; i < s.NumFields(); i++ {
		fmt.Fprintf(w, "%s\n      \"%s\" ::= #%s", sep, getFieldName(i), toCoqName(getFieldName(i)))
		sep = ";"
	}
	fmt.Fprintf(w, "%s", "\n    ]))"+`%struct`+"\n    #(")
	fmt.Fprintf(w, "%s.mk", name)
	for i := 0; i < s.NumFields(); i++ {
		fmt.Fprintf(w, " %s", toCoqName(getFieldName(i)))
	}
	fmt.Fprintf(w, ").\nAdmitted.\n\n")

	if s.NumFields() > 0 {
		// StructFieldsSplit instance
		fmt.Fprint(w, `
Global Instance `+name+`_struct_fields_split dq l (v : `+name+`.t) :
  StructFieldsSplit dq l v (`)
		sep = ""
		for i := 0; i < s.NumFields(); i++ {
			fmt.Fprintf(w, sep+"\n"+
				`    "H`+getFieldName(i)+`" ∷ l ↦s[`+tr.pkg.Name+`.`+name+` :: "`+getFieldName(i)+`"]{dq} v.(`+name+`.`+toCoqName(getFieldName(i))+`)`)
			sep = " ∗"
		}
		fmt.Fprint(w, `
  ).
Admitted.
`)
	}
	fmt.Fprint(w, `
End instances.
`)

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

func translateTypes(w io.Writer, pkg *packages.Package, filter declfilter.DeclFilter) {
	tr := &typesTranslator{
		deps:   deptracker.New(),
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

		for depName := range tr.deps.GetDeps(n) {
			printDefAndDeps(depName)
		}
		fmt.Fprint(w, tr.defs[n])
		printed[n] = true
	}
	for _, d := range tr.defNames {
		printDefAndDeps(d)
	}
}
