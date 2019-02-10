package main

import (
	"fmt"
	"go/ast"
	"go/token"
	"os"
)

// ErrorReporter groups methods for reporting errors, documenting what kind of
// issue was encountered in a uniform way.
type ErrorReporter struct {
	fs *token.FileSet
}

func NewErrorReporter(fs *token.FileSet) ErrorReporter {
	return ErrorReporter{fs}
}

func (r ErrorReporter) prefixed(prefix string, n ast.Node, msg string, args ...interface{}) {
	where := r.fs.Position(n.Pos())
	formatted := fmt.Sprintf(msg, args...)
	fmt.Fprintf(os.Stderr, "%v [%s]: %s\n", where, prefix, formatted)
	// for now make all errors fail-stop
	os.Exit(1)
}

// Nope reports a situation that I thought was impossible from reading the documentation.
func (r ErrorReporter) Nope(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("impossible(go)", n, msg, args...)
}

// NoExample reports a situation I thought was impossible because I couldn't
// think of how to do it in Go.
func (r ErrorReporter) NoExample(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("impossible(no-examples)", n, msg, args...)
}

// FutureWork reports something we could theoretically handle but probably
// won't.
func (r ErrorReporter) FutureWork(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("future", n, msg, args...)
}

// TODO: add a FileSet to ErrorReporter and then report nice filename/line number information

// Todo reports a situation that is intended to be handled but we haven't gotten
// around to.
func (r ErrorReporter) Todo(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("todo", n, msg, args...)
}

// Unsupported reports something intentionally unhandled (the code should not use
// this feature).
func (r ErrorReporter) Unsupported(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("unsupported", n, msg, args...)
}
