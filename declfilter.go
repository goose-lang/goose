package goose

import (
	"github.com/pelletier/go-toml/v2"
)

type declFilter struct {
	isTrivial bool // trivial filter translates everything and has no axioms.

	// describes a cofinite filter on decls.
	toImport     map[string]bool
	toTranslate  map[string]bool
	toAxiomatize map[string]bool
}

func (df *declFilter) includes(name string) bool {
	return df.isTrivial || df.toTranslate[name]
}

func (df *declFilter) includesAxiom(name string) bool {
	return !df.isTrivial && df.toAxiomatize[name]
}

func (df *declFilter) includesImport(name string) bool {
	return df.isTrivial || df.toImport[name]
}

type filterConfig struct {
	Trusted      bool     `toml:"trusted"`
	Imports      []string `toml:"imports"`
	ToTranslate  []string `toml:"translate"`
	ToAxiomatize []string `toml:"axiomatize"`
}

func loadDeclFilter(raw []byte) (bool, declFilter) {
	if raw == nil {
		return false, declFilter{
			isTrivial: true,
		}
	}
	var a filterConfig
	error := toml.Unmarshal(raw, &a)
	if error != nil {
		panic(error.Error())
	}
	if a.Trusted {
		return true, declFilter{}
	}

	var df declFilter = declFilter{
		toImport:     make(map[string]bool),
		toTranslate:  make(map[string]bool),
		toAxiomatize: make(map[string]bool),
	}
	df.isTrivial = false

	for _, name := range a.ToTranslate {
		df.toTranslate[name] = true
	}

	for _, name := range a.Imports {
		df.toImport[name] = true
	}

	for _, name := range a.ToAxiomatize {
		df.toAxiomatize[name] = true
	}
	return false, df
}
