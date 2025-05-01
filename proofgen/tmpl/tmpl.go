package tmpl

import (
	"embed"
	"io"
	"text/template"

	"github.com/pkg/errors"
)

type PackageProof struct {
	Ffi        string
	Name       string
	ImportPath string // import path (corresponding to Go PkgPath)
	HasTrusted bool
	Imports    []Import
	TypesCode  string
	Types      []TypeDecl
	Names      NamesInfo
}

type NamesInfo struct {
	Vars             []Variable
	FunctionNames    []string
	NamedTypeMethods []MethodSet
}

type TypeDecl interface {
	Kind() string
}

type TypeAxiom struct {
	PkgName string
	Name    string
}

func (t TypeAxiom) Kind() string {
	return "axiom"
}

type TypeSimple struct {
	Name string
	Body string
}

func (t TypeSimple) Kind() string {
	return "simple"
}

type TypeStruct struct {
	PkgName string
	Name    string
	Fields  []TypeField
}

func (t TypeStruct) Kind() string {
	return "struct"
}

type TypeField struct {
	Name string
	Type string
}

type Import struct {
	Path string
}

type Variable struct {
	Name    string
	CoqType string
}

type MethodSet struct {
	// a named type, with possible 'ptr suffix for method set of a pointer
	TypeName string
	Methods  []string
}

// Adding a "'" to avoid conflicting with Coq keywords and definitions that
// would already be in context (like `t`). Could do this only when there is a
// conflict, but it's lower entropy to do it always rather than pick and
// choosing when.
func toCoqName(n string) string {
	return n + "'"
}

// isSep returns true if index i is not the last index in a list of length l.
func isSep(i int, l int) bool {
	return i < l-1
}

//go:embed *.tmpl
var tmplFS embed.FS

// loadTemplates is used once to parse the templates. This happens statically,
// using the embed package to get the template files from the source code.
func loadTemplates() *template.Template {
	tmpl := template.New("proofgen").Delims("<<", ">>")
	funcs := template.FuncMap{
		"quote": func(s string) string {
			return `"` + s + `"`
		},
		"coqName": toCoqName,
		"isSep":   isSep,
	}
	tmpl, err := tmpl.Funcs(funcs).ParseFS(tmplFS, "*.tmpl")
	if err != nil {
		panic(errors.Wrap(err, "internal error: templates does not parse"))
	}
	return tmpl
}

var templates *template.Template = loadTemplates()

func (pf PackageProof) Write(w io.Writer) error {
	if err := templates.ExecuteTemplate(w, "package_proof.v.tmpl", pf); err != nil {
		return errors.Wrap(err, "could not emit template")
	}
	return nil
}
