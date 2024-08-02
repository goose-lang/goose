package goose

import (
	"fmt"
	"go/ast"
	"go/token"
	"path"
	"strings"
	"sync"

	"github.com/pkg/errors"

	"github.com/goose-lang/goose/glang"
	"golang.org/x/tools/go/packages"
)

// declsOrError translates one top-level declaration,
// catching Goose translation errors and returning them as a regular Go error
func (ctx Ctx) declsOrError(stmt ast.Decl) (decls []glang.Decl, err error) {
	defer func() {
		if r := recover(); r != nil {
			if gooseErr, ok := r.(gooseError); ok {
				err = gooseErr.err
			} else {
				// r is an error from a non-goose error, indicating a bug
				panic(r)
			}
		}
	}()
	return ctx.maybeDecls(stmt), nil
}

func filterImports(decls []glang.Decl) (nonImports []glang.Decl, imports glang.ImportDecls) {
	for _, d := range decls {
		switch d := d.(type) {
		case glang.ImportDecl:
			imports = append(imports, d)
		default:
			nonImports = append(nonImports, d)
		}
	}
	return
}

type declId struct {
	fileIdx int
	declIdx int
}

// Decls converts an entire package (possibly multiple files) to a list of decls
func (ctx Ctx) decls(fs []*ast.File) (imports glang.ImportDecls, sortedDecls []glang.Decl, errs []error) {
	decls := make(map[string]glang.Decl)
	var declNames []string
	declNameToId := make(map[string]declId)
	imports = make([]glang.ImportDecl, 0)

	// Translate every Go decl into a Glang decl and build up dependencies for
	// each of them.
	for fi, f := range fs {
		for di, d := range f.Decls {
			id := declId{fi, di}
			newDecls, err := ctx.declsOrError(d)
			if err != nil {
				errs = append(errs, err)
			}
			newDecls, newImports := filterImports(newDecls)
			imports = append(imports, newImports...)
			for _, d := range newDecls {
				named, name := d.DefName()
				if !named {
					panic("Unnamed decl")
				}
				declNames = append(declNames, name)
				declNameToId[name] = id
				decls[name] = d
			}
		}
	}

	// Sort Glang decls based on dependencies

	generated := make(map[string]bool)
	generating := make(map[string]bool)
	var processDecl func(name string)
	processDecl = func(name string) {
		if generated[name] {
			return
		}
		if generating[name] {
			id := declNameToId[name]
			errs = append(errs, &ConversionError{
				Category:    "unsupported",
				Message:     fmt.Sprintf("cycle in dependencies while generating %s", name),
				GoCode:      "???",
				GooseCaller: "decls() in interface.go",
				Position:    ctx.fset.Position(fs[id.fileIdx].Decls[id.declIdx].Pos()),
			})
			generated[name] = true
			sortedDecls = append(sortedDecls, decls[name])
			return
		}
		generating[name] = true

		for _, dep := range ctx.dep.nameToDeps[name] {
			if _, ok := decls[dep]; ok {
				processDecl(dep)
			}
		}
		generated[name] = true
		delete(generating, name)
		sortedDecls = append(sortedDecls, decls[name])
	}

	for _, declName := range declNames {
		processDecl(declName)
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

func pkgErrors(errors []packages.Error) error {
	var errs []error
	for _, err := range errors {
		errs = append(errs, err)
	}
	return MultipleErrors(errs)
}

// translatePackage translates an entire package to a single Coq file.
//
// If the source directory has multiple source files, these are processed in
// alphabetical order; this must be a topological sort of the definitions or the
// Coq code will be out-of-order. Sorting ensures the results are stable
// and not dependent on map or directory iteration order.
func translatePackage(pkg *packages.Package) (glang.File, error) {
	if len(pkg.Errors) > 0 {
		return glang.File{}, errors.Errorf(
			"could not load package %v:\n%v", pkg.PkgPath,
			pkgErrors(pkg.Errors))
	}
	ctx := NewPkgCtx(pkg)

	coqFile := glang.File{
		PkgPath:   pkg.PkgPath,
		GoPackage: pkg.Name,
	}
	coqFile.ImportHeader, coqFile.Footer = ffiHeaderFooter(getFfi(pkg))

	imports, decls, errs := ctx.decls(pkg.Syntax)
	coqFile.Imports = imports
	coqFile.Decls = decls
	if len(errs) != 0 {
		return coqFile, errors.Wrap(MultipleErrors(errs),
			"conversion failed")
	}
	return coqFile, nil
}

func ffiHeaderFooter(ffi string) (header string, footer string) {
	if ffi == "none" {
		header = "Section code.\n" +
			"Context `{ffi_syntax}."
		footer = "\nEnd code.\n"
	} else {
		header += fmt.Sprintf("From New Require Import %s_prelude.", ffi)
	}
	return
}

// newPackageConfig creates a package loading configuration suitable for
// Goose translation.
func newPackageConfig(modDir string) *packages.Config {
	mode := packages.NeedName | packages.NeedCompiledGoFiles
	mode |= packages.NeedImports
	mode |= packages.NeedTypes | packages.NeedSyntax | packages.NeedTypesInfo
	return &packages.Config{
		Dir:        modDir,
		Mode:       mode,
		BuildFlags: []string{"-tags", "goose"},
		Fset:       token.NewFileSet(),
	}
}

// TranslatePackages loads packages by a list of patterns and translates them
// all, producing one file per matched package.
//
// The errs list contains errors corresponding to each package (in parallel with
// the files list). patternErr is only non-nil if the patterns themselves have
// a syntax error.
func TranslatePackages(modDir string,
	pkgPattern ...string) (files []glang.File, errs []error, patternErr error) {
	pkgs, err := packages.Load(newPackageConfig(modDir), pkgPattern...)
	if err != nil {
		return nil, nil, err
	}
	if len(pkgs) == 0 {
		// consider matching nothing to be an error, unlike packages.Load
		return nil, nil,
			errors.New("patterns matched no packages")
	}
	files = make([]glang.File, len(pkgs))
	errs = make([]error, len(pkgs))
	var wg sync.WaitGroup
	wg.Add(len(pkgs))
	for i, pkg := range pkgs {
		go func(i int, pkg *packages.Package) {
			f, err := translatePackage(pkg)
			files[i] = f
			errs[i] = err
			wg.Done()
		}(i, pkg)
	}
	wg.Wait()
	return
}
