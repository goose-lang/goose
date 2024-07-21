package goose

import (
	"fmt"
)

// One of these tracks *all* the dependencies for an entire package
type depTracker struct {
	nameToDeps       map[string][]string
	currentNameValid bool
	currentName      string
}

func (dt *depTracker) setCurrentName(s string) {
	if dt.currentNameValid {
		panic(fmt.Sprintf("depTracker: tried to change current name without "+
			"unsetting it first (currently %s, tried to set to %s",
			dt.currentName, s,
		))
	}

	dt.currentName = s
	dt.currentNameValid = true
}

func (dt *depTracker) unsetCurrentName() {
	if !dt.currentNameValid {
		panic("depTracker: tried to unset current name, but none is set")
	}
	dt.currentNameValid = false
	dt.currentName = ""
}

func (dt *depTracker) addDep(s string) {
	dt.nameToDeps[dt.currentName] = append(dt.nameToDeps[dt.currentName], s)
}

func newDepTracker() *depTracker {
	return &depTracker{
		nameToDeps:       make(map[string][]string),
		currentName:      "",
		currentNameValid: false,
	}
}
