package proofgen

import (
	"fmt"
	"go/types"
)

func toCoqType(t types.Type, myPkgPath string) string {
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
		return fmt.Sprintf("(vec %s %d)", toCoqType(t.Elem(), myPkgPath), t.Len())
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
			if myPkgPath == t.Obj().Pkg().Path() {
				return t.Obj().Name() + ".t"
			} else {
				return fmt.Sprintf("%s.%s.t", t.Obj().Pkg().Name(), t.Obj().Name())
			}
		}
		return toCoqType(u, myPkgPath)
	case *types.Struct:
		if t.NumFields() == 0 {
			return "unit"
		} else {
			panic(fmt.Sprint("Anonymous structs with fields are not supported ", t))
		}
	}
	panic(fmt.Sprint("Unknown type ", t))
}
