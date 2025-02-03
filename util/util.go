package util

import (
	"bytes"
	"fmt"
	"go/token"
	"io"
	"os"
	"path"
	"strings"

	"github.com/fatih/color"
	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"golang.org/x/tools/go/packages"
)

type PackageTranslator func(io.Writer, *packages.Package, bool, string, declfilter.DeclFilter)

func newPackageConfig(modDir string) *packages.Config {
	mode := packages.NeedName | packages.NeedCompiledGoFiles
	mode |= packages.NeedImports
	mode |= packages.NeedTypes | packages.NeedSyntax | packages.NeedTypesInfo
	mode |= packages.NeedDeps
	return &packages.Config{
		Dir:  modDir,
		Mode: mode,
		Fset: token.NewFileSet(),
	}
}

// write data to file name, first checking if it already has those contents
//
// like os.WriteFile, creates name if it doesn't exist and doesn't set perm if
// the file does exist
func writeFileIfChanged(name string, data []byte, perm os.FileMode) error {
	contents, err := os.ReadFile(name)
	if err != nil {
		return os.WriteFile(name, data, perm)
	}
	// file has correct contents, return
	if bytes.Compare(contents, data) == 0 {
		return nil
	}
	return os.WriteFile(name, data, perm)
}

var ffiMapping = map[string]string{
	"github.com/mit-pdos/gokv/grove_ffi":         "grove",
	"github.com/goose-lang/primitive/disk":       "disk",
	"github.com/goose-lang/primitive/async_disk": "async_disk",
}

func getFfi(pkg *packages.Package) (bool, string) {
	seenFfis := make(map[string]struct{})
	packages.Visit([]*packages.Package{pkg},
		func(pkg *packages.Package) bool {
			// the dependencies of an FFI are not considered as being used; this
			// allows one FFI to be built on top of another
			if _, ok := ffiMapping[pkg.PkgPath]; ok {
				return false
			}
			return true
		},
		func(pkg *packages.Package) {
			if ffi, ok := ffiMapping[pkg.PkgPath]; ok {
				seenFfis[ffi] = struct{}{}
			}
		},
	)

	if len(seenFfis) > 1 {
		panic(fmt.Sprintf("multiple ffis used %v", seenFfis))
	}
	for ffi := range seenFfis {
		return true, ffi
	}
	return false, ""
}

func Translate(translatePkg PackageTranslator, pkgPatterns []string, outRootDir string, modDir string, configDir string) {
	red := color.New(color.FgRed).SprintFunc()
	pkgs, err := packages.Load(newPackageConfig(modDir), pkgPatterns...)

	if err != nil {
		panic(err)
	} else if len(pkgs) == 0 {
		panic("patterns matched no packages")
	}
	for _, pkg := range pkgs {
		w := new(strings.Builder)

		rawConfig, _ := os.ReadFile(path.Join(
			configDir,
			glang.ImportToPath(pkg.PkgPath)+".toml"),
		)
		filter := declfilter.Load(rawConfig)
		if filter.HasTrusted() {
			continue
		}

		usingFfi, ffi := getFfi(pkg)
		translatePkg(w, pkg, usingFfi, ffi, filter)

		outFile := path.Join(outRootDir, glang.ImportToPath(pkg.PkgPath))
		outDir := path.Dir(outFile)
		err = os.MkdirAll(outDir, 0777)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not create output directory"))
		}
		err = writeFileIfChanged(outFile, []byte(w.String()), 0666)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
	}
}
