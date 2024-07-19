#!/bin/bash

set -eu

usage() {
  echo "Usage: $0 [path to perennial repo]" 1>&2
}

blue=$(tput setaf 4 || printf "")
green=$(tput setaf 2 || printf "")
red=$(tput setaf 1 || printf "")
reset=$(tput sgr0 || printf "")

info() {
  echo -e "${blue}$1${reset}"
}

error() {
  echo -e "${red}$1${reset}" 1>&2
}

good() {
  echo -e "${green}$1${reset}" 1>&2
}

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
REPO="$DIR/.."

perennial_dir=""
while [[ $# -gt 0 ]]; do
  case "$1" in
  -help | --help | -h)
    usage
    exit 0
    ;;
  -*)
    usage
    exit 1
    ;;
  *)
    break
    ;;
  esac
done

if [ $# -gt 0 ]; then
  perennial_dir="$1"
fi

if [ ! -d "$perennial_dir" ]; then
  usage
  if [ "$perennial_dir" = "" ]; then
    error "perennial dir not provided"
  else
    error "Perennial dir does not exist"
  fi
  exit 1
fi

# generate and run the Go side of the tests
cd "$REPO"
go generate ./...
go test -update-gold
go test ./internal/examples/semantics

# generate the Coq side
go run ./cmd/test_gen/main.go -coq \
  -out "$perennial_dir"/etc/../src/goose_lang/interpreter/generated_test.v \
  ./internal/examples/semantics
go run ./cmd/goose -out \
  "$perennial_dir"/etc/../external/Goose \
  -dir ./internal/examples \
  ./semantics ./unittest ./unittest/generic
make -C "$perennial_dir" external/Goose/github_com/goose-lang/goose/internal/examples/unittest.vo
make -C "$perennial_dir" src/goose_lang/interpreter/generated_test.vo
