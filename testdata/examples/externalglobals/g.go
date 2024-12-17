package externalglobals

import (
	"github.com/goose-lang/goose/testdata/examples/unittest"
)

func f() {
	unittest.GlobalX = 11
}
