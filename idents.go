package goose

import (
	"go/ast"
	"go/types"
)

// this file has code that deals with tracking properties about identifiers, when
// Go's type information isn't enough (for example, we treat var declarations
// differently, but Go doesn't expose this since it makes no difference to the
// language)

type identInfo struct {
	// IsMacro is true when an identifier refers to a Gallina definition in the
	// translation (as opposed to a GooseLang variable)
	IsMacro bool
}

type scopedName struct {
	scope *types.Scope
	name  string
}

type identCtx struct {
	info map[scopedName]identInfo
}

func newIdentCtx() identCtx {
	return identCtx{info: make(map[scopedName]identInfo)}
}

func (ctx Ctx) lookupIdentScope(ident *ast.Ident) scopedName {
	obj, ok := ctx.info.Uses[ident]
	if !ok {
		return scopedName{nil, ""}
	}
	useScope := obj.Parent()
	name := ident.Name
	defScope, _ := useScope.LookupParent(name, ident.Pos())
	return scopedName{scope: defScope, name: name}
}

func (idents identCtx) lookupName(scope *types.Scope, name string) identInfo {
	if scope == types.Universe {
		return identInfo{
			// TODO: setting this to true triggers too often
			IsMacro: false,
		}
	}
	info, ok := idents.info[scopedName{scope, name}]
	if ok {
		return info
	}
	return idents.lookupName(scope.Parent(), name)
}

func (ctx Ctx) identInfo(ident *ast.Ident) identInfo {
	if ident.Name == "_" {
		ctx.unsupported(ident, "unexpected use of anonymous identifier")
	}
	scope := ctx.info.Uses[ident].Parent()
	return ctx.idents.lookupName(scope, ident.Name)
}

func (ctx Ctx) doesDefHaveInfo(ident *ast.Ident) bool {
	obj := ctx.info.Defs[ident]
	if obj == nil {
		// ident is not actually a definition (this is what happens when you
		// multiply assign variables and only one of them is fresh - the others
		// are not being defined but just re-assigned)
		return true
	}
	defScope := obj.Parent()
	key := scopedName{scope: defScope, name: ident.Name}
	_, ok := ctx.idents.info[key]
	return ok
}

func (ctx Ctx) addDef(ident *ast.Ident, info identInfo) {
	if ident.Name == "_" {
		return
	}
	obj := ctx.info.Defs[ident]
	defScope := obj.Parent()
	key := scopedName{scope: defScope, name: ident.Name}
	ctx.idents.info[key] = info
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
