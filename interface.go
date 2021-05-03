package goose

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path"
	"sort"
	"strings"

	"github.com/pkg/errors"

	"github.com/tchajed/goose/internal/coq"
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

func sortedFiles(files map[string]*ast.File) []NamedFile {
	var flatFiles []NamedFile
	for n, f := range files {
		flatFiles = append(flatFiles, NamedFile{Path: n, Ast: f})
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
func (config Config) TranslatePackage(pkgPath string, srcDir string) (coq.File, error) {
	// TODO: we might be able to replace this implementation with something
	//  based on go/packages; see https://pkg.go.dev/golang.org/x/tools/go/packages?tab=doc#Package.
	fset := token.NewFileSet()
	filter := func(info os.FileInfo) bool {
		if strings.HasSuffix(info.Name(), "_test.go") {
			return false
		}
		return true
	}
	s, err := os.Stat(srcDir)
	if err != nil {
		return coq.File{},
			fmt.Errorf("source directory %s does not exist", srcDir)
	}
	if !s.IsDir() {
		return coq.File{},
			fmt.Errorf("%s is a Ast (expected a directory)", srcDir)
	}
	packages, err := parser.ParseDir(fset, srcDir, filter, parser.ParseComments)
	if err != nil {
		return coq.File{},
			errors.Wrap(err, "code does not parse")
	}

	if len(packages) > 1 {
		return coq.File{},
			errors.New("found multiple packages")
	}

	var pkgName string
	var files []NamedFile
	for pName, p := range packages {
		files = append(files, sortedFiles(p.Files)...)
		pkgName = pName
	}
	if pkgPath != "" {
		pkgName = pkgPath
	}
	var fileAsts []*ast.File
	for _, f := range files {
		fileAsts = append(fileAsts, f.Ast)
	}

	ctx := NewCtx(pkgName, fset, config)
	err = ctx.TypeCheck(pkgName, fileAsts)
	if err != nil {
		return coq.File{},
			errors.Wrap(err, "code does not type check")
	}

	decls, errs := ctx.Decls(files...)
	err = nil
	if len(errs) != 0 {
		err = errors.Wrap(MultipleErrors(errs), "conversion failed")
	}
	var ih string
	var f string
	if config.Ffi == "none" {
		ih = "Section code.\n" +
			"Context `{ext_ty: ext_types}.\n" +
			"Local Coercion Var' s: expr := Var s."
		f = "\nEnd code.\n"
	} else {
		ih = fmt.Sprintf(FfiImportFmt, config.Ffi)
		f = ""
	}
	return coq.File{GoPackage: pkgName, Decls: decls, ImportHeader: ih, Footer: f}, err
}

const FfiImportFmt string = "From Perennial.goose_lang Require Import ffi.%s_prelude."
