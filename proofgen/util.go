package proofgen

import (
	"fmt"
	"go/types"

	"golang.org/x/tools/go/packages"
)

func basicTypeToCoq(t *types.Basic) string {
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
}

func namedTypeToCoq(t *types.Named, pkg *packages.Package) string {
	objPkg := t.Obj().Pkg()
	thisName := t.Obj().Name()
	if objPkg == nil || pkg.PkgPath == objPkg.Path() {
		n := thisName + ".t"
		return n
	} else {
		n := fmt.Sprintf("%s.%s.t", objPkg.Name(), thisName)
		return n
	}
}

func toCoqType(t types.Type, pkg *packages.Package) string {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		return basicTypeToCoq(t)
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
		return namedTypeToCoq(t, pkg)
	case *types.Struct:
		if t.NumFields() == 0 {
			return "unit"
		} else {
			panic(fmt.Sprintf("Anonymous structs with fields are not supported (%s): %s",
				pkg.Fset.Position(t.Field(0).Pos()).String(),
				t.String()))
		}
	}
	panic(fmt.Sprintf("Unknown type %s (of type %T)", t, t))
}
