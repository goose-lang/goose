package proofgen

import (
	"go/ast"
	"go/token"
	"go/types"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/proofgen/tmpl"
	"golang.org/x/tools/go/packages"
)

type namesTranslator struct {
	pkg *packages.Package

	filter declfilter.DeclFilter

	vars       []tmpl.Variable
	functions  []string
	namedTypes []*types.Named

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
						tr.vars = append(tr.vars, tmpl.Variable{
							Name:    name.Name,
							CoqType: toCoqType(info.TypeOf(name), tr.pkg),
						})
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

func translateNames(pkg *packages.Package, filter declfilter.DeclFilter) tmpl.NamesInfo {
	tr := &namesTranslator{pkg: pkg, filter: filter}

	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}

	info := tmpl.NamesInfo{}

	info.Vars = tr.vars

	for _, funcName := range tr.functions {
		if tr.filter.GetAction(funcName) == declfilter.Skip {
			continue
		}
		info.FunctionNames = append(info.FunctionNames, funcName)
	}

	// emit instances for unfolding method_call
	for _, namedType := range tr.namedTypes {
		baseTypeName := namedType.Obj().Name()
		typeName := namedType.Obj().Name()
		mset := tmpl.MethodSet{
			TypeName: typeName,
		}
		goMset := types.NewMethodSet(namedType)
		for i := range goMset.Len() {
			methodName := goMset.At(i).Obj().Name()
			if tr.filter.GetAction(baseTypeName+"."+methodName) == declfilter.Skip {
				continue
			}
			mset.Methods = append(mset.Methods, methodName)
		}
		info.NamedTypeMethods = append(info.NamedTypeMethods, mset)

		typeName = namedType.Obj().Name() + "'ptr"
		ptrMset := tmpl.MethodSet{
			TypeName: typeName,
		}
		goMset = types.NewMethodSet(types.NewPointer(namedType))
		for i := range goMset.Len() {
			methodName := goMset.At(i).Obj().Name()
			if tr.filter.GetAction(baseTypeName+"."+methodName) == declfilter.Skip {
				continue
			}
			ptrMset.Methods = append(ptrMset.Methods, methodName)
		}
		info.NamedTypeMethods = append(info.NamedTypeMethods, ptrMset)
	}
	return info
}
