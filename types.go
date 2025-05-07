package goose

import (
	"fmt"
	"go/ast"
	"go/types"
	"strconv"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
)

// this file has the translations for types themselves

func (ctx *Ctx) typeSpecIsGooseLang(spec *ast.TypeSpec) bool {
	if spec.TypeParams != nil {
		return true
	}
	if t, ok := ctx.typeOf(spec.Type).Underlying().(*types.Struct); ok {
		if t.NumFields() == 0 {
			return false
		}
		for i := 0; i < t.NumFields(); i++ {
			fieldType := t.Field(i).Type()
			if TypeIsGooseLang(fieldType) {
				return true
			}
		}
	}
	return false
}

// TypeIsGooseLang checks if a type must be translated as GooseLang (due to
// generics); if false, it is translated to a Gallina go_type instead.
func TypeIsGooseLang(t types.Type) bool {
	// note that t.TypeParams() != nil && t.TypeParams().Len() == 0 is possible: it
	// indicates an originally generic, instantiated type
	switch t := t.(type) {
	case *types.Named:
		if t.TypeParams() != nil {
			return true
		}
	case *types.Alias:
		if t.TypeParams() != nil {
			return true
		}
	}
	if t, ok := t.Underlying().(*types.Struct); ok {
		if t.NumFields() == 0 {
			return false
		}
		for i := 0; i < t.NumFields(); i++ {
			fieldType := t.Field(i).Type()
			if TypeIsGooseLang(fieldType) {
				return true
			}
		}
	}
	return false
}

func (ctx *Ctx) typeDecl(spec *ast.TypeSpec) []glang.Decl {
	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Axiomatize:
		// TODO: need to remember this is axiomatized as a go_type
		return []glang.Decl{glang.AxiomDecl{
			DeclName: spec.Name.Name,
			Type:     glang.GallinaIdent("go_type"),
		}}
	case declfilter.Trust:
		if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			if _, ok := t.Underlying().(*types.Interface); !ok {
				ctx.namedTypes = append(ctx.namedTypes, t)
			}
		}
		return nil
	case declfilter.Translate:
		ctx.dep.SetCurrentName(spec.Name.Name)
		defer ctx.dep.UnsetCurrentName()
		if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			if _, ok := t.Underlying().(*types.Interface); !ok {
				ctx.namedTypes = append(ctx.namedTypes, t)
			}
		}
		ty := ctx.typeOf(spec.Type)
		decl := glang.TypeDecl{
			Name:       spec.Name.Name,
			Body:       ctx.glangType(spec, ty),
			TypeParams: ctx.typeParamList(spec.TypeParams),
		}
		if ctx.typeSpecIsGooseLang(spec) {
			return []glang.Decl{decl}
		} else {
			return []glang.Decl{glang.GallinaTypeDecl{
				Decl: decl,
			}}
		}
	default:
		return nil
	}
}

func (ctx *Ctx) typeOf(e ast.Expr) types.Type {
	return ctx.info.TypeOf(e)
}

func (ctx *Ctx) glangTypeFromExpr(e ast.Expr) glang.Type {
	return ctx.glangType(e, ctx.typeOf(e))
}

func (ctx *Ctx) structType(t *types.Struct) glang.Type {
	ty := glang.StructType{}
	for i := range t.NumFields() {
		fieldType := t.Field(i).Type()
		fieldName := t.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_" + strconv.Itoa(i)
		}

		ty.Fields = append(ty.Fields, glang.FieldDecl{
			Name: fieldName,
			Type: ctx.glangType(t.Field(i), fieldType),
		})
	}
	return ty
}

// SimpleType translates t if it is a "simple type" (typically a simple
// identifier, with no structs or generics), returning nil if the type is not
// supported.
func SimpleType(t types.Type) glang.Type {
	t = types.Unalias(t)
	if isProphId(t) {
		return glang.TypeIdent("ProphIdT")
	}
	switch t := t.(type) {
	case *types.Struct:
		return nil
	case *types.TypeParam:
		// might need special handling
		return nil
	case *types.Basic:
		switch t.Name() {
		case "uint64", "uint32", "uint16", "uint8", "int64", "int32", "int16", "int8", "byte", "int", "uint", "bool", "string", "float64", "float32":
			return glang.TypeIdent(fmt.Sprintf("%sT", t.Name()))
		case "untyped string":
			return glang.TypeIdent("stringT")
		}
		return nil
	case *types.Pointer:
		return glang.PtrType{}
	case *types.Named:
		if t.Obj().Pkg() == nil {
			if t.Obj().Name() == "error" {
				return glang.TypeIdent("error")
			}
			return nil // unexpected
		}
		if t.Obj().Pkg().Name() == "filesys" && t.Obj().Name() == "File" {
			return glang.TypeIdent("fileT")
		}
		if t.Obj().Pkg().Name() == "disk" && t.Obj().Name() == "Disk" {
			return glang.TypeIdent("disk.Disk")
		}
		return nil // structs, type arguments, reference to a type
	case *types.Slice:
		// TODO: Value is not actually used
		return glang.SliceType{Value: nil}
	case *types.Map:
		keyT := SimpleType(t.Key())
		valueT := SimpleType(t.Elem())
		if keyT != nil && valueT != nil {
			return glang.MapType{Key: keyT, Value: valueT}
		}
	case *types.Signature:
		return glang.FuncType{}
	case *types.Interface:
		return glang.InterfaceType{}
	case *types.Chan:
		elemT := SimpleType(t.Elem())
		if elemT != nil {
			return glang.ChanType{Elem: elemT}
		}
	case *types.Array:
		elemT := SimpleType(t.Elem())
		if elemT != nil {
			return glang.ArrayType{Len: uint64(t.Len()), Elem: elemT}
		}
	}
	return nil
}

func (ctx *Ctx) glangType(n locatable, t types.Type) glang.Type {
	t = types.Unalias(t)
	if tr := SimpleType(t); tr != nil {
		return tr
	}
	switch t := t.(type) {
	case *types.Struct:
		return ctx.structType(t)
	case *types.TypeParam:
		return glang.GooseLangTypeIdent(t.Obj().Name())
	case *types.Basic:
		// if not handled by SimpleType, unsupported
		ctx.unsupported(n, "basic type %s", t.Name())
	case *types.Pointer:
		return glang.PtrType{}
	case *types.Named:
		if t.Obj().Pkg() == nil {
			ctx.unsupported(n, "unexpected built-in type %v", t.Obj())
		}
		if info, ok := ctx.getStructInfo(t); ok {
			return ctx.structInfoToGlangType(info)
		}
		ctx.dep.Add(ctx.qualifiedName(t.Obj()))
		if t.TypeArgs().Len() != 0 {
			return glang.TypeCallExpr{
				MethodName: glang.TypeIdent(ctx.qualifiedName(t.Obj())),
				Args:       ctx.convertTypeArgsToGlang(nil, t.TypeArgs()),
			}
		}
		return glang.TypeIdent(ctx.qualifiedName(t.Obj()))
	case *types.Map:
		return glang.MapType{Key: ctx.glangType(n, t.Key()), Value: ctx.glangType(n, t.Elem())}
	case *types.Chan:
		return glang.ChanType{Elem: ctx.glangType(n, t.Elem())}
	case *types.Array:
		return glang.ArrayType{Len: uint64(t.Len()), Elem: ctx.glangType(n, t.Elem())}
	}
	ctx.unsupported(n, "unknown type %v", t)
	return nil // unreachable
}

func sliceElem(t types.Type) types.Type {
	if t, ok := t.Underlying().(*types.Slice); ok {
		return t.Elem()
	}
	panic(fmt.Errorf("expected slice type, got %v", t))
}

func ptrElem(t types.Type) types.Type {
	if t, ok := t.Underlying().(*types.Pointer); ok {
		return t.Elem()
	}
	panic(fmt.Errorf("expected pointer type, got %v", t))
}

func isProphId(t types.Type) bool {
	if t, ok := t.(*types.Pointer); ok {
		if t, ok := t.Elem().(*types.Named); ok {
			name := t.Obj()
			return name.Pkg() != nil &&
				name.Pkg().Name() == "machine" &&
				name.Name() == "prophId"
		}
	}
	return false
}

func isByteSlice(t types.Type) bool {
	if t, ok := t.(*types.Slice); ok {
		if elTy, ok := t.Elem().Underlying().(*types.Basic); ok {
			return elTy.Kind() == types.Byte
		}
	}
	return false
}

func isString(t types.Type) bool {
	if t, ok := t.(*types.Basic); ok {
		return t.Kind() == types.String
	}
	return false
}

func (ctx *Ctx) convertTypeArgsToGlang(l locatable, typeList *types.TypeList) (glangTypeArgs []glang.Type) {
	glangTypeArgs = make([]glang.Type, typeList.Len())
	for i := range glangTypeArgs {
		glangTypeArgs[i] = ctx.glangType(l, typeList.At(i))
	}
	return
}

// glang.Expr is an interface that is a subset of glang.Type, but Go has
// requires a conversion (perhaps because there are different runtime
// representations)
func typesToExprs(ts []glang.Type) []glang.Expr {
	var es []glang.Expr
	for _, t := range ts {
		es = append(es, t)
	}
	return es
}

type structTypeInfo struct {
	name           string
	throughPointer bool
	namedType      *types.Named
	structType     *types.Struct
	typeArgs       *types.TypeList
}

func (ctx *Ctx) structInfoToGlangType(info structTypeInfo) glang.Type {
	ctx.dep.Add(info.name)
	if TypeIsGooseLang(info.namedType) {
		return glang.TypeCallExpr{MethodName: glang.GallinaIdent(info.name), Args: ctx.convertTypeArgsToGlang(nil, info.typeArgs)}
	} else {
		return glang.TypeIdent(info.name)
	}
}

func (ctx *Ctx) getStructInfo(t types.Type) (structTypeInfo, bool) {
	throughPointer := false
	if pt, ok := t.(*types.Pointer); ok {
		throughPointer = true
		t = pt.Elem()
	}
	if t, ok := t.(*types.Named); ok {
		name := ctx.qualifiedName(t.Obj())
		if structType, ok := t.Underlying().(*types.Struct); ok {
			return structTypeInfo{
				name:           name,
				typeArgs:       t.TypeArgs(),
				namedType:      t,
				throughPointer: throughPointer,
				structType:     structType,
			}, true
		}
	}
	return structTypeInfo{}, false
}

type interfaceTypeInfo struct {
	name           string
	interfaceType  *types.Interface
	throughPointer bool
}

func (ctx *Ctx) getInterfaceInfo(t types.Type) (interfaceTypeInfo, bool) {
	throughPointer := false
	if pt, ok := t.(*types.Pointer); ok {
		throughPointer = true
		t = pt.Elem()
	}
	if t, ok := t.(*types.Named); ok {
		name := ctx.qualifiedName(t.Obj())
		if interfaceType, ok := t.Underlying().(*types.Interface); ok {
			return interfaceTypeInfo{
				name:           name,
				interfaceType:  interfaceType,
				throughPointer: throughPointer,
			}, true
		}
	}
	return interfaceTypeInfo{}, false
}
