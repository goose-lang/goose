# Writing in Goose

(this document is still to be written)

Reassignments require using `var` instead of `:=` to declare the variable. This
signals to Goose to wrap the local variable in an extra pointer. If you don't
need reassignments avoiding this pointer is nice, hence this odd distinction
(whereas in Go `var` and `:=` are identical).

Loops are subtle - generally you should make sure every return path has an
explicit `break` or `continue`. The translator should be made sound on this
aspect (rejecting unsupported code).

# Supported features

- multiple return values
- early return
- for loops
- slice and map iteration
- panic
- struct field pointers
- struct literals
- slice element pointers
- sub-slicing
- pointers to local variables
- mutexes and cond vars (`*sync.Mutex` and `*sync.Cond`)
- goroutines
- `++` and `+=`
- `uint64`, `uint32`, `byte` (no signed integers are supported)
- bitwise ops
