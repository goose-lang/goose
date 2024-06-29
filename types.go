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

func (ctx Ctx) mapType(e *ast.MapType) glang.MapType {
	ty := ctx.typeOf(e).Underlying().(*types.Map)
	if !supportedMapKey(ty.Key()) {
		ctx.unsupported(e, "maps must be from uint64 or string (not %v)", e.Key)
	}
	return glang.MapType{Key: ctx.coqType(e.Key), Value: ctx.coqType(e.Value)}
}

func (ctx Ctx) selectorExprType(e *ast.SelectorExpr) glang.Expr {
	if isIdent(e.X, "filesys") && isIdent(e.Sel, "File") {
		return glang.TypeIdent("fileT")
	}
	if isIdent(e.X, "disk") && isIdent(e.Sel, "Block") {
		return glang.TypeIdent("disk.blockT")
	}
	return ctx.coqTypeOfType(e, ctx.typeOf(e))
}

func (ctx Ctx) coqTypeOfType(n ast.Node, t types.Type) glang.Type {
	// TODO: move support for various types in ctx.coqType with this function
	//
	// ctx.coqType operates syntactically whereas this function uses type
	// checker info. We can always write ctx.coqType in terms of this function,
	// since the go/types package will give a types.Type expression for the
	// "type" of an Ast.Expr representing a type. Improving this function is
	// also useful because there are some situations where there is no
	// syntactic type and we need to operate on the output of type inference
	// anyway.
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
		return glang.SliceType{Value: ctx.coqTypeOfType(n, t.Elem())}
	case *types.Map:
		return glang.MapType{Key: ctx.coqTypeOfType(n, t.Key()), Value: ctx.coqTypeOfType(n, t.Elem())}
	case *types.Signature:
		return glang.FuncType{}
	case *types.Interface:
		ctx.unsupported(n, "interface type")
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

func (ctx Ctx) arrayType(e *ast.ArrayType) glang.Type {
	if e.Len != nil {
		t := ctx.typeOf(e).(*types.Array)
		return glang.ArrayType{Len: uint64(t.Len()), Elt: ctx.coqType(e.Elt)}
	}
	return glang.SliceType{Value: ctx.coqType(e.Elt)}
}

func (ctx Ctx) ptrType(e *ast.StarExpr) glang.Type {
	return glang.PtrType{}
}

func isEmptyInterface(e *ast.InterfaceType) bool {
	return len(e.Methods.List) == 0
}

func (ctx Ctx) coqType(e ast.Expr) glang.Type {
	switch e := e.(type) {
	case *ast.Ident:
		// FIXME: this treats "e" as denoting a type name if "IsMacro", but
		// otherwise treats it as a Go object and returns its type.
		if _, ok := ctx.info.Uses[e].(*types.Const); ok {
			ctx.dep.addDep(e.Name)
		}
		// if ctx.identInfo(e).IsMacro {
		// 	return glang.TypeIdent(e.Name)
		// }
		return ctx.coqTypeOfType(e, ctx.typeOf(e))
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.SelectorExpr:
		return ctx.selectorExprType(e)
	case *ast.ArrayType:
		return ctx.arrayType(e)
	case *ast.StarExpr:
		return ctx.ptrType(e)
	case *ast.InterfaceType:
		if isEmptyInterface(e) {
			return glang.TypeIdent("anyT")
		} else {
			ctx.unsupported(e, "non-empty interface")
		}
	case *ast.Ellipsis:
		// NOTE: ellipsis types are not fully supported
		// we emit the right type here but Goose doesn't know how to call a method
		// which takes variadic parameters (it'll pass them as separate arguments)
		return glang.SliceType{Value: ctx.coqType(e.Elt)}
	case *ast.FuncType:
		return glang.FuncType{}
	default:
		ctx.unsupported(e, "unexpected type expr")
	}
	return glang.TypeIdent("<type>")
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
		typeArgs = append(typeArgs, ctx.coqTypeOfType(n, ts.At(i)))
	}
	return typeArgs
}
