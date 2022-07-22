package trust_import

import (
	"github.com/tchajed/goose/internal/examples/trust_import/trusted_example"
)

func Bar() {
	trusted_example.Foo()
}
