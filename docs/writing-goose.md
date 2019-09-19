# Writing in Goose

(note that this document is still a work-in-progress)

Imports must be in a short whitelist

Supported types:

- `uint64`
- `byte`
- user-defined structs, defined as a top-level alias
  (this is idiomatic Go - it's also possible to define a field as an anonymous
  struct field, which Goose probably doesn't handle correctly)
- slices of Goose types, that is `[]T` where `T` is a Goose type
- maps from `uint64` to a Goose type, that is `map[uint64]T` where `T` is a
  goose type
- pointers to Goose types, that is `*T` where `T` is a Goose type
- `*sync.RWMutex` (note that these must be pointers; embedding a mutex in a
  struct is not supported)

Functions can return multiple values.

Goose may translate code and then you get an error roughly about a mismatch
between `T` and `proc T'`. This is due to Goose not fully understanding the
effect system of the Coq model, which requires exactly one effectful computation
(that is, one `proc`) per line. If you have two effects on one line of Go, put
one first and assign the result to a variable. If you need to return the value
of a procedure, you need to sequence them:

```go
// bad: will produce Coq code of the form [Ret MyGoFunction], which doesn't work
func f() {
    return MyGoFunction()
}

// good: will produce [v <- MyGoFunction; Ret v], which is what you want
func f() {
    v := MyGoFunction()
    return v
}
```

You may also run into this issue in the opposite direction, where the Goose
translator produces sequencing but the first component is actually pure (that
is, not a Coq `proc`). You can either inline that assignment or improve Goose's
recognition of pure expressions by improving `internal/coq/coq.go`'s `isPure`
function. That function is untrusted - everything is checked by Coq's type
system.
