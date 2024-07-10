package goose

import (
	"fmt"
	"go/ast"
	"go/types"

	"github.com/tchajed/goose/internal/glang"
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

// for now only string and uint64 are supported
//
// literals structs with literals should also be fine
func supportedMapKey(keyTy types.Type) bool {
	if isString(keyTy) {
		return true
	}
	info, ok := getIntegerType(keyTy)
	if ok && info.isUint64() {
		return true
	}
	return false
}

func (ctx Ctx) selectorExprType(e *ast.SelectorExpr) glang.Expr {
	if isIdent(e.X, "filesys") && isIdent(e.Sel, "File") {
		return glang.TypeIdent("fileT")
	}
	if isIdent(e.X, "disk") && isIdent(e.Sel, "Block") {
		return glang.TypeIdent("disk.blockT")
	}
	return ctx.glangType(e, ctx.typeOf(e))
}

func (ctx Ctx) glangTypeFromExpr(e ast.Expr) glang.Type {
	return ctx.glangType(e, ctx.typeOf(e))
}

func (ctx Ctx) glangType(n ast.Node, t types.Type) glang.Type {
	if isProphId(t) {
		return glang.TypeIdent("ProphIdT")
	}
	switch t := t.(type) {
	case *types.Struct:
		ctx.unsupported(n, "type for anonymous struct")
	case *types.TypeParam:
		return glang.TypeIdent(t.Obj().Name())
	case *types.Basic:
		switch t.Name() {
		case "uint64":
			return glang.TypeIdent("uint64T")
		case "uint32":
			return glang.TypeIdent("uint32T")
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
			ctx.unsupported(n, "unexpected built-in type %v", t.Obj())
		}
		if t.Obj().Pkg().Name() == "filesys" && t.Obj().Name() == "File" {
			return glang.TypeIdent("fileT")
		}
		if t.Obj().Pkg().Name() == "disk" && t.Obj().Name() == "Disk" {
			return glang.TypeIdent("disk.Disk")
		}
		if info, ok := ctx.getStructInfo(t); ok {
			ctx.dep.addDep(info.name)
			return glang.StructName(info.name)
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
	}
	// panic("unknown type")
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

func (ctx Ctx) ptrType(_ *ast.StarExpr) glang.Type {
	return glang.PtrType{}
}

func isEmptyInterface(e *ast.InterfaceType) bool {
	return len(e.Methods.List) == 0
}

func isLockRef(t types.Type) bool {
	if t, ok := t.(*types.Pointer); ok {
		if t, ok := t.Elem().(*types.Named); ok {
			name := t.Obj()
			return name.Pkg().Name() == "sync" &&
				name.Name() == "Mutex"
		}
	}
	return false
}

func isCFMutexRef(t types.Type) bool {
	if t, ok := t.(*types.Pointer); ok {
		if t, ok := t.Elem().(*types.Named); ok {
			name := t.Obj()
			return name.Pkg().Name() == "cfmutex" &&
				name.Name() == "CFMutex"
		}
	}
	return false
}

func isCondVar(t types.Type) bool {
	if t, ok := t.(*types.Pointer); ok {
		if t, ok := t.Elem().(*types.Named); ok {
			name := t.Obj()
			return name.Pkg().Name() == "sync" &&
				name.Name() == "Cond"
		}
	}
	return false
}

func isWaitGroup(t types.Type) bool {
	if t, ok := t.(*types.Pointer); ok {
		if t, ok := t.Elem().(*types.Named); ok {
			name := t.Obj()
			return name.Pkg().Name() == "sync" &&
				name.Name() == "WaitGroup"
		}
	}
	return false
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
		if elTy, ok := t.Elem().(*types.Basic); ok {
			return elTy.Name() == "byte"
		}
	}
	return false
}

func isString(t types.Type) bool {
	if t, ok := t.(*types.Basic); ok {
		return t.Name() == "string"
	}
	return false
}

func isDisk(t types.Type) bool {
	if t, ok := t.(*types.Named); ok {
		obj := t.Obj()
		if obj.Pkg().Path() == "github.com/tchajed/goose/machine/disk" &&
			obj.Name() == "Disk" {
			return true
		}
	}
	return false
}

type intTypeInfo struct {
	width     int
	isUntyped bool
}

func (info intTypeInfo) isUint64() bool {
	return info.width == 64 || info.isUntyped
}

func (info intTypeInfo) isUint32() bool {
	return info.width == 32 || info.isUntyped
}

func (info intTypeInfo) isUint8() bool {
	return info.width == 8 || info.isUntyped
}

func getIntegerType(t types.Type) (intTypeInfo, bool) {
	basicTy, ok := t.Underlying().(*types.Basic)
	if !ok {
		return intTypeInfo{}, false
	}
	switch basicTy.Kind() {
	// conversion from uint64 -> uint64 is possible if the conversion
	// causes an untyped literal to become a uint64
	case types.Uint, types.Int, types.Uint64:
		return intTypeInfo{width: 64}, true
	case types.UntypedInt:
		return intTypeInfo{isUntyped: true}, true
	case types.Uint32:
		return intTypeInfo{width: 32}, true
	case types.Uint8:
		return intTypeInfo{width: 8}, true
	default:
		return intTypeInfo{}, false
	}
}

type structTypeInfo struct {
	name           string
	throughPointer bool
	structType     *types.Struct
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
				name:           name,
				throughPointer: throughPointer,
				structType:     structType,
			}, true
		}
	}
	return structTypeInfo{}, false
}

type interfaceTypeInfo struct {
	name          string
	interfaceType *types.Interface
}

func (ctx Ctx) getInterfaceInfo(t types.Type) (interfaceTypeInfo, bool) {
	if pt, ok := t.(*types.Pointer); ok {
		t = pt.Elem()
	}
	if t, ok := t.(*types.Named); ok {
		name := ctx.qualifiedName(t.Obj())
		if interfaceType, ok := t.Underlying().(*types.Interface); ok {
			return interfaceTypeInfo{
				name:          name,
				interfaceType: interfaceType,
			}, true
		}
	}
	return interfaceTypeInfo{}, false
}

func (info structTypeInfo) fields() []string {
	var fields []string
	for i := 0; i < info.structType.NumFields(); i++ {
		fields = append(fields, info.structType.Field(i).Name())
	}
	return fields
}

func (ctx Ctx) typeList(n ast.Node, ts *types.TypeList) []glang.Expr {
	var typeArgs []glang.Expr
	if ts == nil {
		return nil
	}
	for i := 0; i < ts.Len(); i++ {
		typeArgs = append(typeArgs, ctx.glangType(n, ts.At(i)))
	}
	return typeArgs
}
