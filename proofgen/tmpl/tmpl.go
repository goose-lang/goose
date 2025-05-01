package tmpl

import (
	"embed"
	"io"
	"text/template"

	"github.com/pkg/errors"
)

type Import struct {
	Path string
}

type PackageProof struct {
	Ffi        string
	Name       string
	ImportPath string // import path (corresponding to Go PkgPath)
	HasTrusted bool
	Imports    []Import
	TypesCode  string
	Names      NamesInfo
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

type NamesInfo struct {
	Vars             []Variable
	FunctionNames    []string
	NamedTypeMethods []MethodSet
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
