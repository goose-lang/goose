// declfilter defines the configuration (using toml) for how Go is translated to
// GooseLang.
package declfilter

import (
	"github.com/pelletier/go-toml/v2"
)

// FilterConfig defines the format of the toml files
//
// TODO: currently the only way to "wildcard" a config is to not have a toml
// file. Should have something more flexible like glob patterns.
type FilterConfig struct {
	Imports      []string `toml:"imports"`
	Trusted      []string `toml:"trusted"`
	ToTranslate  []string `toml:"translate"`
	ToAxiomatize []string `toml:"axiomatize"`
}

type Action int

const (
	Skip Action = iota
	Translate
	Axiomatize
	Trust
)

// DeclFilter determines how to treat each declaration in a Go package.
type DeclFilter interface {
	GetAction(string) Action
	ShouldImport(string) bool
	HasTrusted() bool
}

type declFilter struct {
	isTrivial bool // trivial filter translates everything and has no axioms.

	toImport     map[string]bool
	toTrust      map[string]bool
	toTranslate  map[string]bool
	toAxiomatize map[string]bool
}

func (df *declFilter) GetAction(name string) Action {
	switch {
	case df.isTrivial, df.toTranslate[name]:
		return Translate
	case df.toAxiomatize[name]:
		return Axiomatize
	case df.toTrust[name]:
		return Trust
	default:
		return Skip
	}
}

func (df *declFilter) ShouldImport(i string) bool {
	return df.isTrivial || df.toImport[i]
}

func (df *declFilter) HasTrusted() bool {
	return len(df.toTrust) > 0
}

func Load(raw []byte) DeclFilter {
	if raw == nil {
		return &declFilter{
			isTrivial: true,
		}
	}
	var a FilterConfig
	error := toml.Unmarshal(raw, &a)
	if error != nil {
		panic(error.Error())
	}
	df := &declFilter{
		toImport:     make(map[string]bool),
		toTranslate:  make(map[string]bool),
		toAxiomatize: make(map[string]bool),
		toTrust:      make(map[string]bool),
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

	for _, name := range a.Trusted {
		df.toTrust[name] = true
	}
	return df
}
