#!/bin/bash

set -eu

export PLANOUT_CONFIG="$(pwd)/../resources/planout.configs" 
export PLANOUT="$(pwd)/../planout/compiler/planout.js"
if ! [ -x "$(command z3)" ]; then
  export PATH="$(pwd)/../z3-4.6.0-x64-ubuntu-14.04/bin:${PATH}"
fi
# Test that Z3 exists!
echo "(set-option :print-success true)" | z3 -in -smt2

./clean.sh

eval $(opam config env)

oasis setup
ocaml setup.ml -configure --enable-tests
ocaml setup.ml -build
ocaml setup.ml -test -runner sequential -verbose true
