package proofgen

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"log"
	"strconv"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/deptracker"
	"github.com/goose-lang/goose/proofgen/tmpl"
	"golang.org/x/tools/go/packages"
)

type typesTranslator struct {
	pkg *packages.Package

	filter declfilter.DeclFilter

	deps *deptracker.Deps
	defs map[string]tmpl.TypeDecl
	// tracks the order definitions were seen in
	defNames []string
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

func (tr *typesTranslator) axiomatizeType(spec *ast.TypeSpec) tmpl.TypeAxiom {
	name := spec.Name.Name
	defName := name + ".t"
	tr.deps.SetCurrentName(defName)
	defer tr.deps.UnsetCurrentName()
	decl := tmpl.TypeAxiom{
		PkgName: tr.pkg.Name,
		Name:    name,
	}
	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = decl
	return decl
}

func (tr *typesTranslator) translateSimpleType(spec *ast.TypeSpec, t types.Type) tmpl.TypeSimple {
	name := spec.Name.Name
	defName := name + ".t"
	tr.deps.SetCurrentName(defName)
	defer tr.deps.UnsetCurrentName()

	typeBody := tr.toCoqTypeWithDeps(t)

	decl := tmpl.TypeSimple{
		Name: name,
		Body: typeBody,
	}
	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = decl
	return decl
}

func (tr *typesTranslator) translateStructType(spec *ast.TypeSpec, s *types.Struct) tmpl.TypeStruct {
	name := spec.Name.Name
	defName := name + ".t"
	tr.deps.SetCurrentName(defName)
	defer tr.deps.UnsetCurrentName()

	decl := tmpl.TypeStruct{
		PkgName: tr.pkg.Name,
		Name:    name,
	}
	for i := 0; i < s.NumFields(); i++ {
		fieldName := s.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_" + strconv.Itoa(i)
		}
		fieldType := tr.toCoqTypeWithDeps(s.Field(i).Type())
		decl.Fields = append(decl.Fields, tmpl.TypeField{
			Name: fieldName,
			Type: fieldType,
		})
	}
	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = decl
	return decl
}

func (tr *typesTranslator) translateType(spec *ast.TypeSpec) {
	switch s := tr.pkg.TypesInfo.TypeOf(spec.Type).(type) {
	case *types.Struct:
		tr.translateStructType(spec, s)
	default:
		tr.translateSimpleType(spec, s)
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

func translateTypes(pkg *packages.Package, filter declfilter.DeclFilter) []tmpl.TypeDecl {
	tr := &typesTranslator{
		deps:   deptracker.New(),
		defs:   make(map[string]tmpl.TypeDecl),
		pkg:    pkg,
		filter: filter,
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}

	var printingOrdered []string
	printing := make(map[string]bool)
	printed := make(map[string]bool)
	var printDefAndDeps func(string)

	var decls []tmpl.TypeDecl
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
		decl, ok := tr.defs[n]
		if ok {
			decls = append(decls, decl)
		}
		printed[n] = true
	}
	for _, d := range tr.defNames {
		printDefAndDeps(d)
	}
	return decls
}
