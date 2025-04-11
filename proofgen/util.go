package proofgen

import (
	"fmt"
	"go/types"

	"golang.org/x/tools/go/packages"
)

func toCoqType(t types.Type, pkg *packages.Package) string {
	// TODO: reduce duplication with toCoqTypeWithDeps
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
		return fmt.Sprintf("(vec %s (uint.nat (W64 %d)))", toCoqType(t.Elem(), pkg), t.Len())
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
			return t.Obj().Name() + ".t"
		} else {
			return fmt.Sprintf("%s.%s.t", t.Obj().Pkg().Name(), t.Obj().Name())
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
