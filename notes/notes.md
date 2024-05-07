---
title: Goose internal documentation
---

# Types
Types in Go have two kinds of impacts:

1. **They restrict which programs can be written.**
Code that fails the Go type checker, such as `x := 1; x = "foo"`, is not in the
set of valid Go programs.
To model Go soundly, there's no need to restrict the set of valid GooseLang
programs. It only means that {goosed Go programs} ⊊ {GooseLang programs}. There
is therefore no notion of a well-typed GooseLang program.

2. **They determine/change the behavior of programs.**
   Types specifically determine the behavior of:
   - data initialization (zero values in Go)
   - data access (e.g. what value is given when loading a field of a struct?)
   - method calls on interface values
   - type assertions/switches

To model Go soundly, it **is** important to model the way that types determine
the behavior of a program.
FIXME: currently, there is a Gallina type `ty`. Gallina terms of type `ty`
represent Go types. To get the GooseLang representation of a zero value for a Go
type, one uses the Gallina function `zero_val : ty -> goose_lang.val`. This
means that part of the translation of Go programs into GooseLang is
implemented in Gallina, e.g. via this `zero_val` function. In the future, Goose
should be consistent about which parts of translation to do in `goose.go` v.s.
in Gallina.

Data initialization is interpreted according to the `zero_val` Gallina function.
Data access is interpreted based on a representation of structs as `descriptor`s
in Gallina.
Interfaces and type assertions/switches are unsupported.

## Declarations
Within a package:

* a type alias `type A = B` will be interpreted as a Gallina definition `Definition A := B.`
* a defined type `T` will be interpreted as a Gallina definition `T : ty`

## Translating types
A Go type will be interpreted as follows:

- array types are unsupported
- struct type: a struct type is defined by a list of field declarations. TODO
- pointer type: `*T` is interpreted as an untyped pointer `ptrT : ty`. Untyped
  pointers provide support for mutually recursive data structures that use
  pointers to refer to one another. E.g. `type A struct { x *B }` and 
  `type B struct { x *A }` 
- 

# Expression

type Foo struct {
}

func (f *Foo) m() {
     fmt.Println("x")
}

func f() Foo {
  // ...
}

func main() {
     f().m()
}
