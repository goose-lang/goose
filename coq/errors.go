package coq

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/printer"
	"go/token"
	"os"
)

// errorReporter groups methods for reporting errors, documenting what kind of
// issue was encountered in a uniform way.
type errorReporter struct {
	fs *token.FileSet
}

func newErrorReporter(fs *token.FileSet) errorReporter {
	return errorReporter{fs}
}

func (r errorReporter) printGo(n ast.Node) string {
	var what bytes.Buffer
	printer.Fprint(&what, r.fs, n)
    return string(what.Bytes())
}

func (r errorReporter) prefixed(prefix string, n ast.Node, msg string, args ...interface{}) {
	where := r.fs.Position(n.Pos())
	what := r.printGo(n)
	formatted := fmt.Sprintf(msg, args...)
	fmt.Fprintln(os.Stderr, where, what)
	fmt.Fprintf(os.Stderr, "\t[%s]: %s\n", prefix, formatted)
	// for now make all errors fail-stop
	os.Exit(1)
}

// Nope reports a situation that I thought was impossible from reading the documentation.
func (r errorReporter) Nope(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("impossible(go)", n, msg, args...)
}

// NoExample reports a situation I thought was impossible because I couldn't
// think of how to do it in Go.
func (r errorReporter) NoExample(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("impossible(no-examples)", n, msg, args...)
}

// FutureWork reports something we could theoretically handle but probably
// won't.
func (r errorReporter) FutureWork(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("future", n, msg, args...)
}

// Todo reports a situation that is intended to be handled but we haven't gotten
// around to.
func (r errorReporter) Todo(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("todo", n, msg, args...)
}

// Unsupported reports something intentionally unhandled (the code should not use
// this feature).
func (r errorReporter) Unsupported(n ast.Node, msg string, args ...interface{}) {
	r.prefixed("unsupported", n, msg, args...)
}
