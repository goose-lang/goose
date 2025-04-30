// declfilter defines the configuration (using toml) for how Go is translated to
// GooseLang.
package declfilter

import (
	"regexp"
	"strings"

	"github.com/pelletier/go-toml/v2"
)

// TODO: describe semantic interpretation for stringSet.

type setOpType int

const (
	setUnion setOpType = iota
	setSubtract
)

type setOp struct {
	t setOpType
	r *regexp.Regexp
}

// A string set described by a sequence of glob patterns.
type stringSet []setOp

func (ss stringSet) contains(s string) bool {
	b := false
	for _, op := range ss {
		if op.r.MatchString(s) {
			switch op.t {
			case setUnion:
				b = true
			case setSubtract:
				b = false
			}
		}
	}
	return b
}

func newOp(pat string) setOp {
	var s setOp
	pattern, negated := strings.CutPrefix(pat, "!")
	if negated {
		s.t = setSubtract
	} else {
		s.t = setUnion
	}

	patternParts := strings.Split(pattern, "*")
	for i := range patternParts {
		patternParts[i] = regexp.QuoteMeta(patternParts[i])
	}
	var err error
	s.r, err = regexp.Compile("^" + strings.Join(patternParts, ".*") + "$")
	if err != nil {
		panic(err)
	}
	return s
}

func sliceMap[Slice ~[]A, A any, B any](s Slice, f func(A) B) []B {
	result := make([]B, len(s))
	for i, v := range s {
		result[i] = f(v)
	}
	return result
}

func newStringSet(s []string) stringSet {
	return sliceMap(s, newOp)
}

// filterConfig defines the format of the toml files
type filterConfig struct {
	Imports      []string `toml:"imports"`
	Trusted      []string `toml:"trusted"`
	ToTranslate  []string `toml:"translate"`
	ToAxiomatize []string `toml:"axiomatize"`
}

type declFilter struct {
	imports      stringSet
	trusted      stringSet
	toTranslate  stringSet
	toAxiomatize stringSet
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

func (df *declFilter) GetAction(name string) Action {
	switch {
	case df.toTranslate.contains(name):
		return Translate
	case df.toAxiomatize.contains(name):
		return Axiomatize
	case df.trusted.contains(name):
		return Trust
	default:
		return Skip
	}
}

func (df *declFilter) ShouldImport(i string) bool {
	return df.imports.contains(i)
}

func (df *declFilter) HasTrusted() bool {
	return len(df.trusted) > 0
}

func Load(raw []byte) DeclFilter {
	var c filterConfig
	if raw != nil {
		error := toml.Unmarshal(raw, &c)
		if error != nil {
			panic(error.Error())
		}
	}

	if len(c.ToTranslate) == 0 {
		c.ToTranslate = []string{"*"}
	}

	if len(c.Imports) == 0 {
		c.Imports = []string{"*"}
	}

	var df declFilter
	df.imports = newStringSet(c.Imports)
	df.toAxiomatize = newStringSet(c.ToAxiomatize)
	df.toTranslate = newStringSet(c.ToTranslate)
	df.trusted = newStringSet(c.Trusted)

	return &df
}
