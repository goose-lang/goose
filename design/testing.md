# Testing the Go model

How do we validate that goose produces a Go model that accurately reflects how its input Go code executes? We want to know that running the Go code produces behavior consistent with the model. The approach you might expect is to run the Go code, run the Go model, and compare the results, for a variety of programs. However, the Go model is a Coq relation and thus isn't natively executable.

This proposal suggests writing an interpreter that is executable and verified to run according to the model (at least it produces one valid execution). Then we can run programs in Go and in the interpreter (after importing them using goose) and compare the results.

## An executable model

Our model is fortunately already mostly executable: it uses a variety of combinators over relations that are mostly executable, with a few exceptions that require special handling.

To close the gap, we will first reflect the per-operation `step` semantics into a data type that makes the relation combinators explicit, then write an interpreter that gives some execution for each combinator.

There are some subtleties in the interpreter. First, its output for any operation can be one of several outcomes:
- produce a new state and return value
- error (because the operation has undefined behavior)
- fail (for example, because non-determinism could not be resolved due to interpreter limitations)
- block (there is no step, for example acquiring a lock that another thread owns)

Second, the interpreter needs to keep track of the state efficiently, so it needs some extra state on the side (eg, to allocate a fresh pointer represented as a number we might track the next pointer)

Finally, how should we run the interpreter? Running in Coq might have prohibitively bad performance. This can be fixed with proper data structures, use of `N` instead of nat, and caching, but at some point testing might require extracting and running the interpreter outside.

## Comparing results

To compare Go to Coq we'll run the Go code and the Coq model (however that works) and compare outputs. To use each test program efficiently we would ideally get multiple outputs from both sides, for example by having them output a log and comparing the output strings.
