# Problem: executable, verified code

[![Build Status](https://travis-ci.org/tchajed/goose.svg?branch=master)](https://travis-ci.org/tchajed/goose)

Goose converts a stylized subset of Go to a program in Argosy. The conversion is _trusted_: we run the Go program but prove properties about the Coq code, so it's important that the semantics of the translated code cover all the behaviors of the running Go. We take a few steps to increase the reliability of goose, for example using the Go and Coq type systems and careful choice of the subset of Go (see below for a more detailed argument).

# Motivation

Our prior projects (in PDOS) have relied on extraction to Haskell paired with a trusted interpreter to produce executable code. A shallow embedding benefits verification easier (the meta logic obviates much of the need for a program logic). Extraction lets us exploit the shallow embedding further by using Coq for the pure parts of the implementation, linking with Haskell code for the effectful parts of the code that can't be expressed in Coq.

However, extraction has given us performance problems in every previous project without significantly reducing trust since we must link with unverified code. We observe that we can continue to use a shallow embedding to make reasoning simpler but don't have to use extraction to run our code.

Goose takes a different approach entirely than extraction. Instead of generating the executable code, we import Go code for reasoning inside Coq. This import or conversion process translates to a shallow embedding and we trust the conversion to model Go's semantics. In VST, for example, you trust the conversion to a deep embedding and its semantics (these are `clightgen` and CompCert's C semantics respectively), plus an untrusted verification framework built on top of the deep embedding (this is the rest of VST).

We benefit from two aspects of goose: first, using Go as the executing language and runtime; and second, writing in the implementation language directly. Using Go gives a smaller runtime well-tuned to systems problems. It's much more manageable than the minefield that is C, more systems-y than Haskell, and simpler as a language than Rust. We get a good ecosystem of profiling tools, libraries, and meta-tools for analyzing Go. Since we write directly in Go, we have control over what runs and can improve and analyze its performance directly.

### Aside: why not use Haskell and extraction?

Extraction has given us problems in every previous project.

The heart of the problem is the difficulty of doing performance debugging on the extracted Haskell code. Performance debugging in Haskell is difficult in general, but even moreso when the running code is auto-generated and too large to be read or edited by a human. Debugging concurrency bottlenecks is even hard. We would often have profiles that implied an optimization wasn't valuable (because the code didn't represent a significant fraction of execution time), but implementing the optimization off of intuition and a hunch turned out to be profitable. This is no way to make a progam faster.

Haskell performance is mysterious and suffers when allocating a lot, which is often unavoidable when writing code in the functional style of Coq.

A secondary problem is the Haskell runtime. The runtime is large (this makes it harder to trust and harder to debug). Concurrency in Haskell doesn't always scale, and debugging scalability bottlenecks is painful; Concurrent Haskell is in fact is not intended for multicore performance but expressiveness (for example, writing non-blocking asynchronous code). Much of the documentation for the Haskell runtime is in out-of-date papers, which still describe the functionality correctly but not implementation details (for example, at the time of the Haskell FFI/concurrency paper GHC only used a single OS thread).

In FSCQ FUSE complicated things (this is not a purely Haskell problem). The gap between Haskell FUSE and the kernel is large (requests go from the kernel's VFS layer, to the FUSE kernel side, then a C FUSE userspace library, then to HFuse and finally to the Haskell file-system; responses are routed back the same way). Haskell FFI has a number of subtleties around performance (though it has a strong focus on correctness), and we concluded it was a scalability bottleneck.

I don't want to give the impression Haskell is a bad language. Ordinary Haskell programs are expressive; performance is not the main appeal of using Haskell. The type system is one of the most sophisticated in a production language. It is possible to write very fast and safe Haskell programs, though probably not via extraction (for example, look at the `ST` monad).
