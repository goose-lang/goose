# goose: Go to Coq conversion

[![Build Status](https://travis-ci.org/tchajed/goose.svg?branch=master)](https://travis-ci.org/tchajed/goose)

Goose converts a stylized subset of Go to a program in Argosy. The conversion is _trusted_: we run the Go program but prove properties about the Coq code. The subset of Go is carefully chosen to make the translation simpler and more trustworthy.
