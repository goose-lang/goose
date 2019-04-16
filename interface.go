package goose

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"sort"
	"strings"

	"github.com/pkg/errors"

	"github.com/tchajed/goose/internal/coq"
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

// TranslatePackage translates an entire package in a directory to a single Coq
// file with all the declarations in the package.
//
// If the source directory has multiple source files, these are processed in
// alphabetical order; this must be a topological sort of the definitions or the
// Coq code will be out-of-order. Realistically files should not have
// dependencies on each other, although sorting ensures the results are stable
// and not dependent on hashmap or directory iteration order.
func (config Config) TranslatePackage(srcDir string) (coq.File, error) {
	fset := token.NewFileSet()
	filter := func(info os.FileInfo) bool {
		if strings.HasSuffix(info.Name(), "_test.go") {
			return false
		}
		return true
	}
	s, err := os.Stat(srcDir)
	if err != nil {
		return nil, fmt.Errorf("source directory %s does not exist", srcDir)
	}
	if !s.IsDir() {
		return nil, fmt.Errorf("%s is a file (expected a directory)", srcDir)
	}
	packages, err := parser.ParseDir(fset, srcDir, filter, parser.ParseComments)
	if err != nil {
		return nil, errors.Wrap(err, "code does not parse")
	}

	if len(packages) > 1 {
		return nil, errors.New("found multiple packages")
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
		return nil, errors.Wrap(err, "code does not type check")
	}

	f, err := ctx.File(files...)
	if err != nil {
		return nil, errors.Wrap(err, "conversion failed")
	}
	return f, nil
}
