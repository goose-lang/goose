package main

import "fmt"

// ErrorReporter groups methods for reporting errors, documenting what kind of
// issue was encountered in a uniform way.
type ErrorReporter struct{}

func (r ErrorReporter) prefixed(prefix, msg string, args ...interface{}) {
	formatted := fmt.Sprintf(msg, args...)
	panic(fmt.Errorf("%s: %s", prefix, formatted))
}

// Docs reports a situation that I thought was impossible from reading the documentation.
func (r ErrorReporter) Docs(msg string, args ...interface{}) {
	r.prefixed("impossible(docs)", msg, args...)
}

// NoExample reports a situation I thought was impossible because I couldn't
// think of how to do it in Go.
func (r ErrorReporter) NoExample(msg string, args ...interface{}) {
	r.prefixed("impossible(no-examples)", msg, args...)
}

// FutureWork reports something we could theoretically handle but probably
// won't.
func (r ErrorReporter) FutureWork(msg string, args ...interface{}) {
	r.prefixed("future", msg, args...)
}

// Todo reports a situation that is intended to be handled but we haven't gotten
// around to.
func (r ErrorReporter) Todo(msg string, args ...interface{}) {
	r.prefixed("todo", msg, args...)
}

// Unhandled reports something intentionally unhandled (the code should not use
// this feature).
func (r ErrorReporter) Unhandled(msg string, args ...interface{}) {
	r.prefixed("unhandled", msg, args...)
}

var error ErrorReporter
