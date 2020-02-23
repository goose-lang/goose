# goose: Go to Coq conversion

[![Build Status](https://travis-ci.org/tchajed/goose.svg?branch=deep)](https://travis-ci.org/tchajed/goose)
[![](https://godoc.org/github.com/tchajed/goose?status.svg)](https://godoc.org/github.com/tchajed/goose)

Goose imports code written in Go into [Perennial](https://github.com/mit-pdos/perennial), a Coq framework for verification of concurrent storage systems. The Go code is a complete Go program, which we can import, run, and benchmark. The Perennial program has a precise semantics in Coq describing its behavior, and we can use Perennial to prove that the code meets its specification.

Goose supports only a stylized subset of Go, and part of the Perennial support includes a model for how Go pointers, slices, and maps work (for example). The conversion is _trusted_: we run the Go program but prove properties about the Coq code. The subset of Go and Perennial model are carefully chosen to make the translation simpler and more trustworthy.

## Demo: an example conversion

To give a flavor of what goose does, let's look at an example:

File `db.go`:

```go
// A Table provides access to an immutable copy of data on the filesystem,
// along with an index for fast random access.
type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}

// CreateTable creates a new, empty table.
func CreateTable(p string) Table {
	index := make(map[uint64]uint64)
	f := filesys.Create(p)
	filesys.Close(f)
	f2 := filesys.Open(p)
	return Table{Index: index, File: f2}
}
```

Goose output:

```coq
Module Table.
  (* A Table provides access to an immutable copy of data on the filesystem,
     along with an index for fast random access. *)
  Record t := mk {
    Index: Map uint64;
    File: File;
  }.
  Global Instance t_zero : HasGoZero t := mk (zeroValue _) (zeroValue _).
End Table.

(* CreateTable creates a new, empty table. *)
Definition CreateTable (p:string) : proc Table.t :=
  index <- Data.newMap uint64;
  f <- FS.create p;
  _ <- FS.close f;
  f2 <- FS.open p;
  Ret {| Table.Index := index;
         Table.File := f2; |}.
```

Goose translates Go structs to Coq records; it uses a module to wrap the fields in their own namespace.

The Coq version of `CreateTable` is written as a definition of type `proc Table.t`. A library called `Goose.base` defines all the support needed for this definition; it pulls in the type `proc T`, an Perennial procedure that returns a value of type `T`. Procedures are written using "bind" notation; to understand the examples all you need to know is that `x <- f; ...` means to run `f` and store the result in the variable `x`, then continue running with the new variable `x`.

Perennial functions using `Goose.base` can call a few primitive operations. Here we see two types of primitives: `Data.newMap` corresponds to creating a map (complete with the type of values), and the `filesys.*` functions in Go are turned into `FS.*` methods in Coq (after lower-casing). The Coq definitions are primitives that form the Goose API, and include heap-manipulating functions `Data.*` as well as a filesystem API under `FS.`. The filesystem API is one provided by Goose via the `github.com/tchajed/goose/machine/filesys` package.

Finally, the CreateTable function ends with `Ret` for the return statement in Go. It constructs a `Table.t` literal in much the same way as the Go code, using Coq's support for records.

## Go support

Goose doesn't support arbitrary Go code; it uses a carefully-selected subset of Go that is still idiomatic Go (for the most part) while being easy to translate. See the [implementation design doc](docs/implementation.md) for more details.

There are three aspects of the Go model worth mentioning here:

- Assignments are not supported, only bindings. This imposes a "linearity" restriction where each variable is constant after being first defined, which aligns well with how Perennial code works. Mutable variables can still be emulated using pointers and heap allocation.
- Goose supports a few common control flow patterns so code can be written with early returns and some loops.
- Many operations are carefully modeled as being non-linearizable in Perennial, although this area is subtle and hard to reconcile with Go's documented memory model.

## Related approaches

Goose solves the problem of using Perennial to verify runnable systems while ensuring some connection between the verification and the code. How else do verification projects get executable code?

_Extraction_ is a popular approach, especially in Coq. Extraction is much like compilation in that Coq code is translated to OCaml or Haskell, relying on many similarities between the languages. (Side note: the reason it's called extraction is that it also does _proof erasure_, where proofs mixed into Coq code are removed so they don't have to be run.) To get side effects in extracted code the verification engineers write an interpreter in the target language that runs the verified part, using the power of the target language to interact with the outside world (eg, via the console, filesystem, or network stack).

A big disadvantage of extraction is performance. The source code is several steps away from the extracted code and interpreter. This distance makes it hard to debug performance problems and reduces developers' control over what the running code does.

Another approach is to use a deeply-embedded language that closely represents an efficient imperative language, such as C. Then one can write code directly in this language (eg, Cogent), produce it as part of proof-producing synthesis (eg, Fiat Cryptography), import it from normal source code (eg, `clightgen` for VST). Regardless of how the code in the language is produced, this approach requires a model of the syntax and semantics of the language at a fairly low-level, including modeled function calls, variable bindings, and local stacks, not to mention concurrency and side effects.

Directly modeling a low-level, imperative language (and especially writing in it) gives a great deal of control, which is good for performance. This approach is also well-suited to end-to-end verification: at first, one can pretty-print the imperative language and use any compiler, but eventually one can shift to a verified compiler and push the assumptions down the software stack.

## Running goose

Goose requires Go 1.12 or 1.13.

You can install goose with either `go get github.com/tchajed/goose/cmd/goose
` or from a clone of this repo with `go install ./cmd/goose`. These install
 the `goose` binary to `$GOPATH/bin` (or `~/go/bin` if you don't have GOPATH
set).

To run `goose` on one of the internal examples and update the Coq output in
 Perennial, run (for the append_log example):

```
goose -out $perennial/src/goose_lang/examples/append_log.v \
  ./internal/examples/append_log
```

where `$perennial` is the path to a clone of [Perennial](https://github.com/mit-pdos/perennial).

## Developing goose

The bulk of goose is implemented in `goose.go` (which translates Go) and
`internal/coq/coq.go` (which has structs to represent Coq and GooseLang code,
and code to convert these to strings).

Goose has integration tests that translate example code and compare against a
"gold" file in the repo. Changes to these gold files are hand-audited when
they are initially created, and then the test ensures that previously-working
code continues to translate correctly. To update the gold files after
modifying the tests or fixing goose, run `go test -update-gold` (and manually
review the diff before committing).

The tests include `internal/examples/unittest`, a collection of small
examples intended for wide coverage, as well as some real programs in other
directories within `internal/examples`.

The Coq output is separately tested by building it within the [Perennial
](github.com/mit-pdos/perennial) source tree.

Additionally, the `internal/examples/semantics` package contains a set of
semantic tests for checking that translated programs preserve their semantic
meaning. The testing infrastructure requires test functions to have the form
`func test*() bool` and return true (that is, they begin with "test", take no
arguments, and return a bool expected to always be true). Any helper functions
should _not_ follow this pattern.

The `cmd/test_gen/main.go` file generates the required test files from these
functions. The files are:

- A `.go` file which uses the Go `testing` package. This is for confirming that
  tests actually do always return true, as intended. Note that the use of the
  testing package means that this file must end in `_test.go`. It should go in
  the `semantics/` directory.
- A `.v` file that runs using Perennial's semantic interpreter. This file
  should go in Perennial's `goose_lang/interpreter/` directory and can have any name.

To generate these files, the executable takes a required flag of either `-go`
or `-coq` which specifies the file type, an optional `-out` argument specifying
where to write the output, and finally the path to the semantics package. For
example,
`cmd/test_gen/test_gen -coq -out /.../goose_lang/interpreter/generated_test.v /.../goose/internal/examples/semantics`
generates the Coq file of semantic tests. To re-generate the Go test file you
can run `go generate ./...`.
