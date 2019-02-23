package goose

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"sort"
	"strings"

	"github.com/tchajed/goose/coq"
)

// File converts an entire package (possibly multiple files) to a coq.File
// (which is just a list of declarations)
func (ctx Ctx) File(fs ...*ast.File) (file coq.File, err error) {
	defer func() {
		if r := recover(); r != nil {
			if r, ok := r.(gooseError); ok {
				err = r.err
			} else {
				panic(r)
			}
		}
	}()
	var decls []coq.Decl
	for _, f := range fs {
		if f.Doc != nil {
			decls = append(decls, coq.NewComment(f.Doc.Text()))
		}
		for _, d := range f.Decls {
			if d := ctx.maybeDecl(d); d != nil {
				decls = append(decls, d)
			}
		}
	}
	return coq.File(decls), nil
}

type TranslationError struct {
	Message string
	Err     error
}

func (e *TranslationError) Error() string {
	if e.Err == nil {
		return e.Message
	}
	return fmt.Sprintf("%s\n%s", e.Message, e.Err)
}

type fileName struct {
	name string
	file *ast.File
}

func sortedFiles(files map[string]*ast.File) []*ast.File {
	var flatFiles []fileName
	for n, f := range files {
		flatFiles = append(flatFiles, fileName{name: n, file: f})
	}
	sort.Slice(flatFiles, func(i, j int) bool {
		return flatFiles[i].name < flatFiles[j].name
	})
	var sortedFiles []*ast.File
	for _, f := range flatFiles {
		sortedFiles = append(sortedFiles, f.file)
	}
	return sortedFiles
}

func (config Config) TranslatePackage(srcDir string) (coq.File, *TranslationError) {
	fset := token.NewFileSet()
	filter := func(info os.FileInfo) bool {
		if strings.HasSuffix(info.Name(), "_test.go") {
			return false
		}
		return true
	}
	packages, err := parser.ParseDir(fset, srcDir, filter, parser.ParseComments)
	if err != nil {
		return nil, &TranslationError{
			Message: "code does not parse",
			Err:     err,
		}
	}

	if len(packages) > 1 {
		return nil, &TranslationError{Message: "found multiple packages"}
	}

	var pkgName string
	var files []*ast.File
	for pName, p := range packages {
		files = append(files, sortedFiles(p.Files)...)
		pkgName = pName
	}

	ctx := NewCtx(fset, config)
	err = ctx.TypeCheck(pkgName, files)
	if err != nil {
		return nil, &TranslationError{
			Message: "code does not type check",
			Err:     err,
		}
	}

	f, err := ctx.File(files...)
	if err != nil {
		return nil, &TranslationError{
			Message: "failed to convert to Coq",
			Err:     err,
		}
	}
	return f, nil
}
