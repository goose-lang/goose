# goose: Go to Coq conversion

[![Build Status](https://travis-ci.org/tchajed/goose.svg?branch=master)](https://travis-ci.org/tchajed/goose)
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

Goose translates Go structs to Coq records; it uses a module to provide better namespacing for the fields.

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
