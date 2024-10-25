package goose

import (
	"fmt"
	"go/ast"
	"go/types"

	"github.com/goose-lang/goose/glang"
)

// this file has the translations for types themselves

func (ctx Ctx) typeOf(e ast.Expr) types.Type {
	return ctx.info.TypeOf(e)
}

func (ctx Ctx) getType(e ast.Expr) (typ types.Type, ok bool) {
	typ = ctx.typeOf(e)
	ok = typ != types.Typ[types.Invalid]
	return
}

func (ctx Ctx) glangTypeFromExpr(e ast.Expr) glang.Type {
	return ctx.glangType(e, ctx.typeOf(e))
}

func (ctx Ctx) structType(t *types.Struct) glang.Type {
	ty := glang.StructType{}
	for i := range t.NumFields() {
		fieldt := t.Field(i).Type()
		ty.Fields = append(ty.Fields, glang.FieldDecl{
			Name: t.Field(i).Name(),
			Type: ctx.glangType(t.Field(i), fieldt),
		})
	}
	return ty
}

func (ctx Ctx) glangType(n locatable, t types.Type) glang.Type {
	if isProphId(t) {
		return glang.TypeIdent("ProphIdT")
	}
	switch t := t.(type) {
	case *types.Struct:
		return ctx.structType(t)
	case *types.TypeParam:
		return glang.TypeIdent(t.Obj().Name())
	case *types.Basic:
		switch t.Name() {
		case "uint64":
			return glang.TypeIdent("uint64T")
		case "uint32":
			return glang.TypeIdent("uint32T")
		case "uint8":
			return glang.TypeIdent("uint8T")
		case "int64":
			return glang.TypeIdent("int64T")
		case "int32":
			return glang.TypeIdent("int32T")
		case "int8":
			return glang.TypeIdent("int8T")
		case "byte":
			return glang.TypeIdent("byteT")
		case "bool":
			return glang.TypeIdent("boolT")
		case "string", "untyped string":
			return glang.TypeIdent("stringT")
		case "int":
			return glang.TypeIdent("intT")
		default:
			ctx.unsupported(n, "basic type %s", t.Name())
		}
	case *types.Pointer:
		return glang.PtrType{}
	case *types.Named:
		if t.Obj().Pkg() == nil {
			if t.Obj().Name() == "error" {
				return glang.TypeIdent("error")
			} else {
				ctx.unsupported(n, "unexpected built-in type %v", t.Obj())
			}
		}
		if t.Obj().Pkg().Name() == "filesys" && t.Obj().Name() == "File" {
			return glang.TypeIdent("fileT")
		}
		if t.Obj().Pkg().Name() == "disk" && t.Obj().Name() == "Disk" {
			return glang.TypeIdent("disk.Disk")
		}
		if info, ok := ctx.getStructInfo(t); ok {
			ctx.dep.addDep(info.gallinaIdent.Name.Coq(false))
			return info.gallinaIdent
		}
		ctx.dep.addDep(ctx.qualifiedName(t.Obj()))
		return glang.TypeIdent(ctx.qualifiedName(t.Obj()))
	case *types.Slice:
		return glang.SliceType{Value: ctx.glangType(n, t.Elem())}
	case *types.Map:
		return glang.MapType{Key: ctx.glangType(n, t.Key()), Value: ctx.glangType(n, t.Elem())}
	case *types.Signature:
		return glang.FuncType{}
	case *types.Interface:
		return glang.TypeIdent("interfaceT")
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
			return name.Pkg().Name() == "machine" &&
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

type intTypeInfo struct {
	width     int
	isUntyped bool
}

func getIntegerType(t types.Type) (intTypeInfo, bool) {
	basicTy, ok := t.Underlying().(*types.Basic)
	if !ok {
		return intTypeInfo{}, false
	}
	switch basicTy.Kind() {
	case types.Uint, types.Int, types.Uint64, types.Int64:
		return intTypeInfo{width: 64}, true
	case types.UntypedInt:
		return intTypeInfo{isUntyped: true}, true
	case types.Uint32, types.Int32:
		return intTypeInfo{width: 32}, true
	case types.Uint8, types.Int8:
		return intTypeInfo{width: 8}, true
	default:
		return intTypeInfo{}, false
	}
}

func (ctx Ctx) convertTypeArgsToGlang(l locatable, typeList *types.TypeList) (glangTypeArgs []glang.Type) {
	glangTypeArgs = make([]glang.Type, typeList.Len())
	for i := range glangTypeArgs {
		glangTypeArgs[i] = ctx.glangType(l, typeList.At(i))
	}
	return
}

type structTypeInfo struct {
	throughPointer bool
	structType     *types.Struct
	gallinaIdent   glang.GallinaIdentGeneric
}

func (ctx Ctx) getStructInfo(t types.Type) (structTypeInfo, bool) {
	throughPointer := false
	if pt, ok := t.(*types.Pointer); ok {
		throughPointer = true
		t = pt.Elem()
	}
	if t, ok := t.(*types.Named); ok {
		name := ctx.qualifiedName(t.Obj())
		if structType, ok := t.Underlying().(*types.Struct); ok {
			return structTypeInfo{
				gallinaIdent: glang.GallinaIdentGeneric{
					Name:     glang.GallinaIdent(name),
					TypeArgs: ctx.convertTypeArgsToGlang(nil, t.TypeArgs()),
				},
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

func (ctx Ctx) getInterfaceInfo(t types.Type) (interfaceTypeInfo, bool) {
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
