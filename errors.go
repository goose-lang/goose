package goose

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/printer"
	"go/token"
	"os"
	"runtime"
)

// errorReporter groups methods for reporting errors, documenting what kind of
// issue was encountered in a uniform way.
type errorReporter struct {
	fset *token.FileSet
}

func newErrorReporter(fset *token.FileSet) errorReporter {
	return errorReporter{fset}
}

func (r errorReporter) printGo(n ast.Node) string {
	var what bytes.Buffer
	printer.Fprint(&what, r.fset, n)
	return string(what.Bytes())
}

func getCaller(skip int) string {
	_, file, line, ok := runtime.Caller(1 + skip)
	if !ok {
		return "<no caller>"
	}

	return fmt.Sprintf("%s:%d", file, line)
}

func (r errorReporter) prefixed(prefix string, n ast.Node, msg string, args ...interface{}) {
	where := r.fset.Position(n.Pos())
	what := r.printGo(n)
	formatted := fmt.Sprintf(msg, args...)

	fmt.Fprintf(os.Stderr, "[%s]: %s\n", prefix, formatted)
	fmt.Fprintf(os.Stderr, "%s\n", what)
	fmt.Fprintf(os.Stderr, "\t%s\n", getCaller(2))
	fmt.Fprintf(os.Stderr, "\tsrc: %s\n", where)
	// for now make all errors fail-stop
	// TODO: be able to catch errors in tests in a structured way to support negative tests
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
