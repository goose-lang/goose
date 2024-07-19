# Design documentation

[Motivation](motivation.md) documents why we use the approach of converting from Go at all in the context of our verification work.

[Implementation](implementation.md) walks through the design decisions in the Goose implementation. This includes details on the subset of Go supported, measure to make the translation more trustworthy, and goose works together with a Go support library (the `github.com/goose-lang/goose/machine` and `github.com/tchjaed/goose/machine/filesys` packages) and the Perennial Goose support code in Coq.

[Writing Goose](writing-goose.md) explains how to write code in Goose, the
subset of Go that the Goose translator and Goose model accept.

## Proposals

[Testing the Go mode](testing-proposal.md) is a proposal for validating that the combination of goose with the Go model reflects what the Go code actually does, using empirical tests.
