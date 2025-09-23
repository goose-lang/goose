package glang

// This file has the structs to represent types in GooseLang and Gallina.

import (
	"fmt"
)

// FieldDecl is a name:type declaration in a struct definition
type FieldDecl struct {
	Name string
	Type Expr
}

type StructType struct {
	Fields []FieldDecl
}

func (d StructType) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("structT [")
	pp.Indent(2)
	for i, fd := range d.Fields {
		sep := ";"
		if i == len(d.Fields)-1 {
			sep = ""
		}
		pp.Add("%s :: %s%s", quote(fd.Name), fd.Type.Coq(false), sep)
	}
	pp.Indent(-2)
	pp.AddLine("]")
	return addParens(needs_paren, pp.Build())
}

type TypeDecl struct {
	Name       string
	Body       Expr
	TypeParams []string
}

func (d TypeDecl) DefName() (bool, string) {
	return true, d.Name
}

func (d TypeDecl) CoqDecl() string {
	var pp buffer

	typeParams := ""
	for _, t := range d.TypeParams {
		typeParams += fmt.Sprintf("(%s : go_type) ", t)
	}

	pp.Add("Definition %s %s: go_type := %s.", GallinaIdent(d.Name).Coq(false), typeParams, d.Body.Coq(false))
	pp.Add("#[global] Typeclasses Opaque %s.", GallinaIdent(d.Name).Coq(false))
	pp.Add("#[global] Opaque %s.", GallinaIdent(d.Name).Coq(false))
	return pp.Build()
}

type MapType struct {
	Key   Expr
	Value Expr
}

func (t MapType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaVerbatim("mapT"), t.Key, t.Value).Coq(needs_paren)
}

type ChanType struct {
	Elem Expr
}

// Coq is the GooseLang type
func (t ChanType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaVerbatim("chanT"), t.Elem).Coq(needs_paren)
}

type FuncType struct{}

func (t FuncType) Coq(needs_paren bool) string {
	return "funcT"
}

type InterfaceType struct{}

func (t InterfaceType) Coq(needs_paren bool) string {
	return "interfaceT"
}

type SliceType struct {
	Value Expr
}

func (t SliceType) Coq(needs_paren bool) string {
	return "sliceT"
}

type ArrayType struct {
	Len  uint64
	Elem Expr
}

func (t ArrayType) Coq(needs_paren bool) string {
	len_e := NewCallExpr(GallinaVerbatim("W64"), IntToZ(int64(t.Len)))
	return NewCallExpr(GallinaVerbatim("arrayT"), len_e, t.Elem).Coq(needs_paren)
}

type PtrType struct{}

func (t PtrType) Coq(needs_paren bool) string {
	return "ptrT"
}
