package proofsetup

import (
	"bytes"
	"fmt"
	"path"
	"slices"
	"strings"
	"text/template"

	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/util"
	"github.com/pkg/errors"
	"golang.org/x/tools/go/packages"
)

// Initial plan: emit skeleton file and its correct path for copy-pasting
//
// Eventually, try to update a proof file, especially imports and new WP lemmas.

type ProofSetup struct {
	ProofPath   string
	PackageName string
	Imports     string
	ContextVars string
	WpLemmas    []string
}

// Coq qualified name for a package. Typically called on (pkg.PkgPath, pkg.Name).
func pkgImport(pkgPath string, pkgName string) string {
	fsPath := glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(path.Dir(pkgPath))
	importPrefix := strings.ReplaceAll(fsPath, "/", ".")
	if !strings.Contains(pkgPath, "/") {
		return pkgName
	}
	return importPrefix + "." + pkgName
}

func pkgCoqImports(pkg *packages.Package) []string {
	ffi := util.GetFfi(pkg)
	var imports []string
	for _, p := range pkg.Imports {
		imports = append(imports,
			fmt.Sprintf("New.proof.%s", pkgImport(p.PkgPath, p.Name)))
	}
	slices.Sort(imports)
	ffiImportName := ffi
	if ffi == "" {
		ffiImportName = "proof"
	}
	imports = append(imports,
		fmt.Sprintf("New.proof.%s_prelude", ffiImportName))
	imports = append(imports,
		fmt.Sprintf("New.generatedproof.%s", pkgImport(pkg.PkgPath, pkg.Name)))
	return imports
}

func importToRequireImport(coqPkgName string) string {
	i := strings.LastIndex(coqPkgName, ".")
	if i < 0 {
		panic(errors.Errorf("unexpected coqPkgName %s", coqPkgName))
	}
	return fmt.Sprintf("From %s Require Import %s.", coqPkgName[:i], coqPkgName[i+1:])
}

func New(pkg *packages.Package) ProofSetup {
	ffi := util.GetFfi(pkg)
	s := ProofSetup{
		PackageName: pkg.Name,
	}

	s.ProofPath = path.Join(
		"new/proof/",
		glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(path.Dir(pkg.PkgPath)),
		pkg.Name+".v",
	)

	var importLines []string
	imports := pkgCoqImports(pkg)
	for _, coqName := range imports {
		importLines = append(importLines, importToRequireImport(coqName))
	}
	s.Imports = strings.Join(importLines, "\n")

	if ffi == "" {
		s.ContextVars = "Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}."
	} else {
		s.ContextVars = "Context `{hG: !heapGS Σ} `{!goGlobalsGS Σ}."
	}

	s.WpLemmas = packageWps(pkg)

	return s
}

func (pf ProofSetup) SkeletonFile() string {
	tmpl := template.Must(template.New("proof.v").Parse(`{{.Imports}}

Section proof.
{{.ContextVars}}

#[global] Program Instance : IsPkgInit {{.PackageName}} := ltac2:(build_pkg_init ()).

{{ range $lemma := .WpLemmas -}}
{{$lemma}}
Proof. Admitted.

{{ end -}}
End proof.
`))
	s := new(bytes.Buffer)
	err := tmpl.Execute(s, pf)
	if err != nil {
		panic(fmt.Errorf("internal error: executing template: %v", err))
	}
	return s.String()
}
