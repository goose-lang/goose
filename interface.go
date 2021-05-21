package goose

import (
	"fmt"
	"go/ast"
	"path"
	"sort"
	"strings"

	"github.com/pkg/errors"

	"github.com/tchajed/goose/internal/coq"
	"golang.org/x/tools/go/packages"
)

// declsOrError translates one top-level declaration,
// catching Goose translation errors and returning them as a regular Go error
func (ctx Ctx) declsOrError(stmt ast.Decl) (decls []coq.Decl, err error) {
	defer func() {
		if r := recover(); r != nil {
			if r, ok := r.(gooseError); ok {
				err = r.err
			} else {
				panic(r)
			}
		}
	}()
	return ctx.maybeDecls(stmt), nil
}

func filterImports(decls []coq.Decl) (nonImports []coq.Decl, imports coq.ImportDecls) {
	for _, d := range decls {
		switch d := d.(type) {
		case coq.ImportDecl:
			imports = append(imports, d)
		default:
			nonImports = append(nonImports, d)
		}
	}
	return
}

// Decls converts an entire package (possibly multiple files) to a list of decls
func (ctx Ctx) Decls(fs ...NamedFile) (decls []coq.Decl, errs []error) {
	var imports coq.ImportDecls
	for _, f := range fs {
		if len(fs) > 1 {
			decls = append(decls,
				coq.NewComment(fmt.Sprintf("%s", f.Name())))
		}
		if f.Ast.Doc != nil {
			decls = append(decls, coq.NewComment(f.Ast.Doc.Text()))
		}
		for _, d := range f.Ast.Decls {
			newDecls, err := ctx.declsOrError(d)
			if err != nil {
				errs = append(errs, err)
			}
			newDecls, newImports := filterImports(newDecls)
			decls = append(decls, newDecls...)
			imports = append(imports, newImports...)
		}
	}
	if len(imports) > 0 {
		decls = append([]coq.Decl{imports}, decls...)
	}
	return
}

type MultipleErrors []error

func (es MultipleErrors) Error() string {
	var errs []string
	for _, e := range es {
		errs = append(errs, e.Error())
	}
	errs = append(errs, fmt.Sprintf("%d errors", len(es)))
	return strings.Join(errs, "\n\n")
}

type NamedFile struct {
	Path string
	Ast  *ast.File
}

func (f NamedFile) Name() string {
	return path.Base(f.Path)
}

func sortedFiles(fileNames []string, fileAsts []*ast.File) []NamedFile {
	var flatFiles []NamedFile
    if len(fileNames) != len(fileAsts) {
		fmt.Printf("names: %+v\n", fileNames)
		fmt.Printf("asts: %+v\n", fileAsts)
		panic("sortedFiles(): fileNames must match fileAsts")
    }
	for i := range fileNames {
		flatFiles = append(flatFiles, NamedFile{Path: fileNames[i], Ast: fileAsts[i]})
	}
	sort.Slice(flatFiles, func(i, j int) bool {
		return flatFiles[i].Path < flatFiles[j].Path
	})
	return flatFiles
}

// TranslatePackage translates an entire package in a directory to a single Coq
// Ast with all the declarations in the package.
//
// If the source directory has multiple source files, these are processed in
// alphabetical order; this must be a topological sort of the definitions or the
// Coq code will be out-of-order. Realistically files should not have
// dependencies on each other, although sorting ensures the results are stable
// and not dependent on map or directory iteration order.
func (config Config) TranslatePackage(modDir string, pkgPattern string) ([]coq.File, error) {

	// Want to use the per-package Fset anyways
	pkgs, err := packages.Load(&packages.Config{Dir:modDir, Mode:packages.LoadFiles | packages.LoadSyntax, Fset:nil}, pkgPattern)
	if err != nil {
		return nil, err
	}
	if len(pkgs) == 0 {
		return nil, fmt.Errorf("Could not find matches for package %s", pkgPattern)
	}
	var coqFiles []coq.File
	for _, pkg := range pkgs {
		var ctx Ctx
		ctx, err = NewCtx(pkg)
		if err != nil {
			return nil, err // FIXME: collect errors?
		}
		files := sortedFiles(pkg.CompiledGoFiles, pkg.Syntax)

		decls, errs := ctx.Decls(files...)
		if len(errs) != 0 {
			// FIXME: collect all errors?
			err = errors.Wrap(MultipleErrors(errs), "conversion failed")
		}
		c := coq.File{GoPackage: pkg.PkgPath, Decls: decls, ImportHeader: "", Footer: ""}
		if err != nil { // FIXME: collect all errors?
			return coqFiles, err
		}
		coqFiles = append(coqFiles, c)
	}
	return coqFiles, err
}
