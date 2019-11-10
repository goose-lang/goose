# Implementation

Goose translates struct definitions and functions. The design aims for a simple implementation and secondarily for natural Go code.

When we talk about converting to "Coq" in goose what we really mean is translating `struct` definitions to Coq records and functions to `proc`s in Perennial using the Goose operations.

We made a conscious decision not to model a local environment in Coq. As a result we can translate Go's variable declarations using `:=` to Coq immutable bindings; values can never change since re-assignments in Go are not supported. This greatly simplifies goose: it can translate Go declarations to bindings in a nearly one-to-one manner.

An important aspect of goose's design is that it uses the `go/ast` and `go/types` packages for analyzing Go. The former ensures that we use well-tested tools for parsing and inspecting Go; this both leads to a simpler implementation of goose and increases trust in at least the parsing aspect. We also use `go/types` and typecheck before translation. This ensures that goose has a global, type-checked view of code (references must be resolved in a way goose understands, so it's harder to accidentally hide running code) and means the translation process can be type-directed in a couple places. For example, indexing in Go can represent either slice indexing or map loops; goose distinguishes these two using the type of the object being indexed.

In Coq a binding is also the only way to sequence effectful operations. Go has no such restriction and sequences effects within expressions. For the most part goose code must sequence explicitly (possible lifting expressions out to bindings). Goose has a feature to make this less painful which is to heuristically turn pure bindings into Coq `let` bindings. The analysis is based entirely on the root of the expression. Mistakes in the purity analysis or goose code that accidentally embeds an effectful operation result in type errors in Coq.

A serious difference between Go and Coq is that Go has function-scoped structural control flow whereas `proc` is a value (albeit in a monad). Where this shows up is that there is no direct translation for `return`; `Ret` puts a value in the monad but does not terminate execution. As a result we must be careful to arrange for `return` statements to translate to the last expression in the Coq value. Goose supports a few patterns explicitly but this code is tricky and there are probably other patterns that could also be translated with caution. Some support is necessary for the Go code to be natural; for example, early returns are common and avoid deep nesting.

Loops are a particularly tricky example of control flow that is difficult to translate. Our solution is to support a rigid but usable loop pattern. Loops must:

- have a single loop variable, initialized in the init expression of the `for` loop
- every branch of the loop must terminate with either `break` or an assignment to the loop variable followed by `continue`
- have no nested loops

This pattern supports a natural translation to a Coq `Loop` with a loop variable and unit return value. The argument to `Loop` is the body of the `for` loop with the loop variable bound using `(fun x => ...)`. It's also flexible in Go; the loop variable can be a struct to support multiple values, and loops do not need to be the last statement in a function.

Goose code does not allow outside imports other than its libraries and `sync.RWMutex`. Primitives (eg, `len` and `make`) are explicitly translated when they have analogous operations in the Coq model.

Goose code is particularly rigid about outside operations. Goose includes the `github.com/tchajed/goose/machine/filesys` package that implements the operations modeled by `Filesys.v` and the `github.com/tchajed/goose/machine` supports a few operations besides built-in data structures. These, along with a few built-in functions, are all the external code goose permits.

Some Go features that are not supported include `defer`, `panic`, channels, anonymous functions, taking the address of variables, and re-assignments.

## Go support library

Goose supplies `github.com/tchajed/goose/machine` for a handful of additional base operations (eg, for encoding integers as bytes) and `github.com/tchajed/goose/machine/filesys` for interacting with the filesystem. The filesystem layer is specific to the Perennial concurrent key-value store's needs and thus supports a subset of operations and only a single directory.

## Coq support

Goose translates to a `proc` using the `Goose.GoLayer` layer, which models the Go heap (pointers, slices, and maps) and the Goose `filesys` package. All of the native Go operations are intended to model features built-in to the language. The filesystem model applies only to our `filesys` package, which aims carefully to be a thin wrapper around system calls.

Most operations are modeled as being non-atomic using a trick that makes concurrent writes and reads an error. This is because Go's slices, pointers, and maps are not thread-safe; even pointers are not thread safe since they don't use x86's atomic read and write instructions (which are more expensive than the non-atomic versions). The only safe model of these operations, which can do anything in Go, is to use Perennial "error" transition, the equivalent of undefined behavior in the style of C. The filesystem operations are largely atomic (assuming the kernel does the appropriate synchronization), except for `List`, which might make multiple calls to read a directory.

Go maps deserve some special attention because they need iteration. We handle this iteration using a combination of support from goose and Coq. First, we model non-atomic iteration (that is, iteration where concurrent writes are unsafe) using `MapStartIter` and `MapEndIter` surrounding the actual body. Second, goose recognizes iterations over maps. It translates them to a call to a helper function in Coq that encapsulates the entire pattern of `MapStartIter`, calling the body of the loop on every key-value pair, and finally calling `MapEndIter`.
