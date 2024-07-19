package trust_import

import (
	"github.com/goose-lang/goose/internal/examples/trust_import/trusted_example"
)

func Bar() {
	trusted_example.Foo()
}
