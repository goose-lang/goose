// unittest has two package comments
package unittest

import "github.com/tchajed/marshal"

// Note that compiling this test in Coq relies on the external marshal package
// being compiled and available.

type wrapExternalStruct struct {
	e marshal.Enc
	d marshal.Dec
}

func (w wrapExternalStruct) moveUint64() {
	w.e.PutInt(w.d.GetInt())
}
