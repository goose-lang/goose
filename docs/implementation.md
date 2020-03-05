# Implementation

Goose translates Go functions to GooseLang definitions. Since GooseLang is a lambda calculus with effects, this creates a mismatch with the function-based control flow in Go, and thus control flow is not perfectly supported (particularly for loops, which must be translated to anonymous recursive definitions).

Structs are represented shallowly in GooseLang as tuples of individual fields. However, the in-memory representation of structs flattens the fields into several pointers, each of a "base literal" (eg, integers, booleans, and pointers). This is important since it means we can faithfully represent pointers to struct fields. To make this convenient, structs have a "descriptor" that maps field names to an offset within the struct as well as the expected type at that location. As a result the goose-translated code uses field names, and this is implemented in GooseLang as a struct library within Perennial.

The translation takes into account Go's memory model. This memory model more or less says races are not allowed, so the semantics of loads and stores GooseLang makes racy access to the same pointer undefined behavior. This makes it even more important to make struct fields independent pointers, so that it isn't considered racy to simultaneously access different fields of the same struct from multiple threads.

A few Go features are implemented as libraries in GooseLang on top of simpler primitives. These include slices (using raw pointers), maps (using general sums), and locks (using compare-and-exchange).

## Go support library

Goose supplies `github.com/tchajed/goose/machine` for a handful of additional base operations (eg, for encoding integers as bytes), which have a corresponding semantics in GooseLang (via an implementation).
