package goose

import (
	"go/ast"
	"go/types"
)

// This file gives extra info about identifiers.
// E.g., it helps track ptr wrapping, which Go doesn't easily expose
// since it's not visible in the language.

type identCtx struct {
	isPtrWrapped map[types.Object]bool
}

func newIdentCtx() identCtx {
	return identCtx{isPtrWrapped: make(map[types.Object]bool)}
}

func (ctx Ctx) isGlobalVar(ident *ast.Ident) bool {
	obj := ctx.getObj(ident)
	return obj.Pkg() != nil && obj.Parent() == obj.Pkg().Scope()
}

func (ctx Ctx) isPtrWrapped(ident *ast.Ident) bool {
	obj := ctx.getObj(ident)
	isWrapped, ok := ctx.idents.isPtrWrapped[obj]
	if !ok {
		return false
	}
	return isWrapped
}

func (ctx Ctx) setPtrWrapped(ident *ast.Ident) {
	obj := ctx.getObj(ident)
	ctx.idents.isPtrWrapped[obj] = true
}

func (ctx Ctx) getObj(ident *ast.Ident) types.Object {
	obj := ctx.info.Uses[ident]
	if obj == nil {
		obj = ctx.info.Defs[ident]
	}
	if obj == nil {
		ctx.unsupported(ident, "type checker doesn't have info about this ident")
	}
	return obj
}

func (ctx Ctx) isStruct(ident *ast.Ident) bool {
	obj := ctx.getObj(ident)
	_, ok := obj.Type().Underlying().(*types.Struct)
	return ok
}

func getIdent(e ast.Expr) (ident string, ok bool) {
	if ident, ok := e.(*ast.Ident); ok {
		return ident.Name, true
	}
	return "", false
}

func isIdent(e ast.Expr, ident string) bool {
	i, ok := getIdent(e)
	return ok && i == ident
}
