package proofgen

import (
	"fmt"
	"go/types"
	"strings"

	"golang.org/x/tools/go/packages"
)

func basicTypeToCoq(t *types.Basic) (string, error) {
	switch t.Name() {
	case "uint64", "int64":
		return "w64", nil
	case "uint32", "int32", "rune":
		return "w32", nil
	case "uint16", "int16":
		return "w16", nil
	case "uint8", "int8", "byte":
		return "w8", nil
	case "uint", "int":
		return "w64", nil
	case "float64":
		return "w64", nil
	case "bool":
		return "bool", nil
	case "string", "untyped string":
		return "go_string", nil
	case "Pointer", "uintptr":
		return "loc", nil
	default:
		return "", fmt.Errorf("Unknown basic type %s", t.Name())
	}
}

func namedTypeToCoq(t *types.Named, pkg *packages.Package) (string, error) {
	objPkg := t.Obj().Pkg()
	thisName := t.Obj().Name()
	var baseName string
	if objPkg == nil || pkg.PkgPath == objPkg.Path() {
		baseName = thisName + ".t"
	} else {
		baseName = fmt.Sprintf("%s.%s.t", objPkg.Name(), thisName)
	}
	// if TypeParams() is not nil, there are type parameters in the base named type
	if t.TypeParams() != nil {
		var params []string
		// if there are no type arguments in this instantiation, we still need to
		// pass a unit since the GooseLang type val is a thunk
		if t.TypeArgs().Len() == 0 {
			params = append(params, "#()")
		}
		for i := 0; i < t.TypeArgs().Len(); i++ {
			typ, err := ToCoqType(t.TypeArgs().At(i), pkg)
			if err != nil {
				return "", err
			}
			params = append(params, typ)
		}
		return fmt.Sprintf("(%s %s)", baseName, strings.Join(params, " ")), nil
	}
	return baseName, nil
}

// ToCoqType converts a type to a Gallina type modeling that type
func ToCoqType(t types.Type, pkg *packages.Package) (string, error) {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		return basicTypeToCoq(t)
	case *types.Slice:
		return "slice.t", nil
	case *types.Array:
		typ, err := ToCoqType(t.Elem(), pkg)
		return fmt.Sprintf("(vec %s (uint.nat (W64 %d)))", typ, t.Len()), err
	case *types.Pointer:
		return "loc", nil
	case *types.Signature:
		return "func.t", nil
	case *types.Interface:
		return "interface.t", nil
	case *types.Map, *types.Chan:
		return "loc", nil
	case *types.Named:
		return namedTypeToCoq(t, pkg)
	case *types.Struct:
		if t.NumFields() == 0 {
			return "unit", nil
		} else {
			return "", fmt.Errorf("Anonymous structs with fields are not supported (%s): %s",
				pkg.Fset.Position(t.Field(0).Pos()).String(),
				t.String())
		}
	}
	return "", fmt.Errorf("Unknown type %s (of type %T)", t, t)
}
