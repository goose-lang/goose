# Future work

Some things Goose could support which we have an idea of how to support:

## First-class functions

These can probably be translated to GooseLang functions and things will just
work. However, scoping is tricky and there are corner cases to work out.

## General control flow

To fully support control flow we need a notion of the current function. The
simplest solution to these issues is to translate to continuation-passing style,
where every function takes an explicit continuation and calls it, thus making
the end of the function a first-class object. This easily extends to loops,
which just introduce more continuations. The biggest issue is that it changes
the notion of a Go function from a nice GooseLang function to a CPS function,
which will require a different style of specification. In theory the notation
for Hoare triples can more or less hide this, though. Instead of just
quantifying over a postcondition in "Texan triples" we would quantify over a
continuation that meets the arbitrary postcondition, given the current
function's postcondition: `{P} e {Q}` is written `forall k Φ, P -* (Q -* WP k Φ) -* WP e k Φ`

## Defer

Defer is actually quite complicated in Go, because it can be executed
_dynamically_ (for example, it's possible to queue up defers in a loop). The
semantics of `defer f()` is more or less to add `f` (thunked) to a per-function
defer stack, and then at each return point of the surrounding function to
execute everything in the defer stack. This wouldn't be too bad to add with
continuation-passing style, but the reasoning principle might be complicated
(what property should the user be proving about the defer stack?). On the other
hand, 90% of the use of defers is simply to unlock a mutex, which we could
support in a simpler way.

## Channels

Channels simply require a library implementing them in GooseLang. The library
need not be efficient or have the same scheduling behavior as Go, as long as it
over-approximates the Go behaviors. What makes this a bit tricky is that
channels have many different use cases and features (for example, buffered vs
unbuffered and blocking vs non-blocking sends). We would also need reasoning
principles, though Actris is the right starting point (with some extensions
since Actris assumes much more primitive channels than Go provides).

## Interfaces

There are two aspects to interfaces: dynamic dispatch and type switches. Dynamic
dispatch is simple: an interface value is a bundle of the interfaces' methods
(implemented as a tuple, same as structs), as first-class functions. Go relies
on an interface value to call an interface method, and we can call it by simply
looking it up in the method bundle.

Type switches are a bit more complicated, since Go supports inspecting the
dynamic type of an interface value. Note that this isn't merely in the type
system but requires dynamic semantics. To implement it we would first need to
associate some identifier to each type, then store that identifier and the
underlying type representation alongside the interface methods. (Note in the
special case of `interface{}`, there are no methods, only a type identifier and
data.) Type switches then simply compare the runtime type with the expected
type.

It should work to use the fully-qualified name of each type as its identifier,
comparing with string comparison.

## Recursive structs

To support recursive structs, descriptors should be a list of `Rec (f:string) | NonRec (f:string) (t:ty)`. One issue is that descriptors are no longer quite
inductive, since the recursive occurrence needs to refer to the entire original
list. We would need to take care to unfold recursion at the top level
appropriately.
