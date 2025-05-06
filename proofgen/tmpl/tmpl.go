package tmpl

import (
	"embed"
	"io"
	"iter"
	"strings"
	"text/template"

	"github.com/pkg/errors"
)

// PackageProof is the data that is passed to the top-level package_proof.v.tmpl
// template.
type PackageProof struct {
	Name       string
	Ffi        string
	ImportPath string // import path (corresponding to Go PkgPath)
	HasTrusted bool
	Imports    []Import
	Types      []TypeDecl
	Names      NamesInfo
}

type NamesInfo struct {
	Vars             []Variable
	FunctionNames    []string
	NamedTypeMethods []MethodSet
}

type TypeDecl struct {
	PkgName string
	Name    string
	TypeInfo
}

func (t TypeDecl) GoTypeName() string {
	return t.PkgName + "." + t.Name
}

type TypeInfo interface {
	Kind() string
}

type TypeAxiom struct{}

func (t TypeAxiom) Kind() string {
	return "axiom"
}

type TypeSimple struct {
	Body string
}

func (t TypeSimple) Kind() string {
	return "simple"
}

type TypeStruct struct {
	Fields []TypeField
}

func (t TypeStruct) Kind() string {
	return "struct"
}

func (t TypeStruct) FieldsExceptLast() []TypeField {
	if len(t.Fields) == 0 {
		return nil
	}
	return t.Fields[:len(t.Fields)-1]
}

type TypeField struct {
	Name string
	Type string
}

func (f TypeField) CoqName() string {
	return toCoqName(f.Name)
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

type SepItem[T any] struct {
	X   T
	Sep string
}

// Iterate over a list and wrap each item with a SepItem struct that provides a
// .Sep field when in between elements (that is, for all but the last item of
// the list).
func IterSep[T any](sep string, l []T) iter.Seq[SepItem[T]] {
	return func(yield func(SepItem[T]) bool) {
		for i, x := range l {
			item := SepItem[T]{X: x, Sep: ""}
			if i < len(l)-1 {
				item.Sep = sep
			}
			if !yield(item) {
				return
			}
		}
	}
}

func indent(n int) string {
	return strings.Repeat(" ", n)
}

//go:embed *.tmpl
var tmplFS embed.FS

// loadTemplates is used once to parse the templates. This happens statically,
// using the embed package to get the template files from the source code.
func loadTemplates() *template.Template {
	tmpl := template.New("proofgen")
	funcs := template.FuncMap{
		"indent":        indent,
		"coqName":       toCoqName,
		"isSep":         isSep,
		"iterSepFields": IterSep[TypeField],
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
