package goose

import (
	"go/ast"
)

func getIdent(e ast.Expr) (ident string, ok bool) {
	if ident, ok := e.(*ast.Ident); ok {
		return ident.Name, true
	}
	return "", false
}

func isIdent(e ast.Expr, name string) bool {
	if ident, ok := e.(*ast.Ident); ok {
		return ident.Name == name
	}
	return false
}
