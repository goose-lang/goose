# goose: Go to Coq conversion

[![Build Status](https://travis-ci.org/tchajed/goose.svg?branch=master)](https://travis-ci.org/tchajed/goose)

Goose imports code written in Go into [Armada](https://github.com/mit-pdos/armada), a framework for verification of concurrent storage systems. The Go code is a complete Go program, which we can import, run, and benchmark. The Armada program has a precise semantics in Coq describing its behavior, and we can use the tools in Armada to prove that the code meets its specification.

Goose supports only a stylized subset of Go, and part of the Armada support includes a model for how Go pointers, slices, and maps work (for example). The conversion is _trusted_: we run the Go program but prove properties about the Coq code. The subset of Go is carefully chosen to make the translation simpler and more trustworthy, and the model in Armada is more restrictive than Go in some places to make it more simpler.

## Demo: an example conversion

To give a flavor of what goose looks like, let's look at an example:

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

The Coq version of `CreateTable` is written as a definition of type `proc Table.t`. A library called `Goose.base` defines all the support needed for this definition; it pulls in the type `proc T`, an Armada function that returns a value of type `T`. Functions are written using "bind" notation; to understand the examples all you need to know is that `x <- f; ...` means to run `f` and store the result in the variable `x`, then continue running with the new variable `x`.

Armada functions using `Goose.base` can call a few primitive operations. Here we see two types of primitives: `Data.newMap` corresponds to creating a map (complete with the type of values), and the `filesys.*` functions in Go are turned into `FS.*` methods in Coq (after lower-casing). The Coq definitions are primitives that form the Goose API, and include heap-manipulating functions `Data.*` as well as a filesystem API under `FS.`. The filesystem API is one provided by Goose via the `github.com/tchajed/goose/machine/filesys` package.

Finally, the CreateTable function ends with `Ret` for the return statement in Go. It constructs a `Table.t` literal in much the same way as the Go code, using Coq's support for records.
