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

type A struct {
	Imports      []string
	ToTranslate  []string
	ToAxiomatize []string
}

func loadDeclFilter(raw []byte) declFilter {
	if raw == nil {
		return declFilter{
			isTrivial: true,
		}
	}
	var a A
	error := toml.Unmarshal(raw, &a)
	var df declFilter
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

	if error != nil {
		panic(error)
	}
	return df
}
