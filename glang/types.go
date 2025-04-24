package glang

// This file has the structs to represent types in GooseLang and Gallina.

import (
	"fmt"
)

// Type represents some Go type.
type Type interface {
	// Coq generates the GooseLang code for a type
	Coq(needs_paren bool) string
	// Gallina generates the Gallina version of a type (for use in proofs)
	Gallina(needs_paren bool) string
}

// GallinaType converts a Type to an Expr that converts using the Gallina form
// of the type
type GallinaType struct {
	Ty Type
}

func (t GallinaType) Coq(needs_paren bool) string {
	return t.Ty.Gallina(needs_paren)
}

type TypeCallExpr struct {
	MethodName Expr
	Args       []Type
}

func NewTypeCallExpr(methodName Expr, args ...Type) TypeCallExpr {
	return TypeCallExpr{
		MethodName: methodName,
		Args:       args,
	}
}

var _ Type = TypeCallExpr{}

func (t TypeCallExpr) Coq(needs_paren bool) string {
	// defer to CallExpr's Coq() implementation (we need to create a new slice to go
	// from one interface to another)
	var args []Expr
	if len(t.Args) == 0 {
		args = append(args, UnitLiteral{})
	}
	for _, arg := range t.Args {
		args = append(args, arg)
	}
	return CallExpr{
		MethodName: t.MethodName,
		Args:       args,
	}.Coq(needs_paren)
}

func (t TypeCallExpr) Gallina(needs_paren bool) string {
	// partially defer to CallExpr (because both GooseLang and Gallina have the
	// same syntax for function calls), but use the Gallina() conversion for all the arguments
	var args []Expr
	for _, arg := range t.Args {
		args = append(args, GallinaType{Ty: arg})
	}
	return CallExpr{
		// MethodName already incorporates whether to convert as a GallinaIdent or a
		// GooseLang ident
		MethodName: t.MethodName,
		Args:       args,
	}.Coq(needs_paren)
}

// FieldDecl is a name:type declaration in a struct definition
type FieldDecl struct {
	Name string
	Type Type
}

type StructType struct {
	Fields []FieldDecl
}

var _ Type = StructType{}

func (d StructType) Gallina(needs_paren bool) string {
	var pp buffer
	pp.Add("structT [")
	pp.Indent(2)
	for i, fd := range d.Fields {
		sep := ";"
		if i == len(d.Fields)-1 {
			sep = ""
		}
		pp.Add("%s :: %s%s", quote(fd.Name), fd.Type.Gallina(false), sep)
	}
	pp.Indent(-2)
	pp.AddLine("]")
	return addParens(needs_paren, pp.Build())
}

// Coq is the GooseLang type
func (d StructType) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("type.structT [")
	pp.Indent(2)
	for i, fd := range d.Fields {
		sep := ";"
		if i == len(d.Fields)-1 {
			sep = ""
		}
		pp.Add("(#%s, %s)%s", StringLiteral{fd.Name}.Coq(false), fd.Type.Coq(false), sep)
	}
	pp.Indent(-2)
	pp.AddLine("]")
	return addParens(needs_paren, pp.Build())
}

type TypeDecl struct {
	Name       string
	Body       Type
	TypeParams []TypeIdent
}

func typeBinders(xs []TypeIdent) string {
	var args []string
	for _, a := range xs {
		args = append(args, string(a))
	}
	return bindings(args)
}

func (d TypeDecl) CoqDecl() string {
	var pp buffer
	pp.Add("Definition %s : val := ", d.Name)
	pp.Add("λ: %s, %s.", typeBinders(d.TypeParams), d.Body.Coq(false))
	return pp.Build()
}

func (d TypeDecl) DefName() (bool, string) {
	return true, d.Name
}

// GallinaTypeDecl represents the same information as a TypeDecl, but translates
// as a go_type.
type GallinaTypeDecl struct {
	Decl TypeDecl
}

func (gd GallinaTypeDecl) CoqDecl() string {
	d := gd.Decl
	var pp buffer

	typeParams := ""
	for _, t := range d.TypeParams {
		typeParams += fmt.Sprintf("(%s: go_type) ", t.Coq(false))
	}

	pp.Add("Definition %s %s: go_type := %s.", d.Name, typeParams, d.Body.Gallina(false))
	return pp.Build()
}

func (gd GallinaTypeDecl) DefName() (bool, string) {
	return gd.Decl.DefName()
}

// Construct a Golang expression for a type.
//
// This handles the difference between a Gallina `go_type` (which has to be
// converted to an expression with #) and type identifiers (which are already expressions).
func GolangTypeExpr(t Type) Expr {
	return t
}

// TypeIdent is a Gallina identifier referencing a type.
type TypeIdent string

var _ Type = TypeIdent("")

// Coq is the GooseLang type
func (t TypeIdent) Coq(needs_paren bool) string {
	return fmt.Sprintf("#%s", string(t))
}

func (t TypeIdent) Gallina(needs_paren bool) string {
	return string(t)
}

type GooseLangTypeIdent string

var _ Type = GooseLangTypeIdent("")

// Coq is the GooseLang type
func (t GooseLangTypeIdent) Coq(needs_paren bool) string {
	return quote(string(t))
}

func (t GooseLangTypeIdent) Gallina(needs_paren bool) string {
	// such an identifier will never make sense in Gallina
	panic("GooseLangTypeIdent should not be used in Gallina")
}

type MapType struct {
	Key   Type
	Value Type
}

var _ Type = MapType{}

// Coq is the GooseLang type
func (t MapType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaIdent("type.mapT"), t.Key, t.Value).Coq(needs_paren)
}

func (t MapType) Gallina(needs_paren bool) string {
	return NewTypeCallExpr(GallinaIdent("mapT"), t.Key, t.Value).Gallina(needs_paren)
}

type ChanType struct {
	Elem Type
}

// Coq is the GooseLang type
func (t ChanType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaIdent("type.chanT"), t.Elem).Coq(needs_paren)
}

func (t ChanType) Gallina(needs_paren bool) string {
	return NewTypeCallExpr(GallinaIdent("chanT"), t.Elem).Gallina(needs_paren)
}

type FuncType struct{}

var _ Type = FuncType{}

func (t FuncType) Coq(needs_paren bool) string {
	return "#funcT"
}

func (t FuncType) Gallina(needs_paren bool) string {
	return "funcT"
}

type InterfaceType struct{}

var _ Type = InterfaceType{}

func (t InterfaceType) Coq(needs_paren bool) string {
	return "#interfaceT"
}
func (t InterfaceType) Gallina(needs_paren bool) string {
	return "interfaceT"
}

type SliceType struct {
	Value Type
}

var _ Type = SliceType{}

func (t SliceType) Coq(needs_paren bool) string {
	return "#sliceT"
}

func (t SliceType) Gallina(needs_paren bool) string {
	return "sliceT"
}

type ArrayType struct {
	Len  uint64
	Elem Type
}

var _ Type = ArrayType{}

// Coq is the GooseLang type
func (t ArrayType) Coq(needs_paren bool) string {
	len_e := Int64Val{IntToZ(int64(t.Len))}
	return NewCallExpr(GallinaIdent("type.arrayT"), len_e, t.Elem).Coq(needs_paren)
}

func (t ArrayType) Gallina(needs_paren bool) string {
	len_e := NewCallExpr(GallinaIdent("W64"), IntToZ(int64(t.Len)))
	return NewCallExpr(GallinaIdent("arrayT"), len_e, GallinaType{t.Elem}).Coq(needs_paren)
}

type PtrType struct{}

var _ Type = PtrType{}

// Coq is the GooseLang type
func (t PtrType) Coq(needs_paren bool) string {
	return "#ptrT"
}

func (t PtrType) Gallina(needs_paren bool) string {
	return "ptrT"
}
