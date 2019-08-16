#!/bin/bash

set -x
set -eu

# Variables
OPAMPKGS="ocamlbuild=0.12.0 ocamlfind=1.7.3 oasis=0.4.10 ounit=2.0.7 yojson=1.4.0 dolog=3.0 core=v0.10.0 async_unix=v0.10.0 yaml=0.1.0 ppx_deriving=4.2.1 ppx_sexp_conv=v0.10.0 ppx_fields_conv=v0.10.0" 
PLANOUT_CONFIG="./resources/planout.configs" 
DISPLAY=":0.0" 
Z3URL=https://github.com/Z3Prover/z3/releases/download/z3-4.5.0/z3-4.6.0-x64-ubuntu-14.04.zip
export PLANOUT="$(pwd)/planout/compiler/planout.js" 

# This was missing config before. Not sure if that was intentional
eval `opam config env`

# Ocaml and opam setup
echo "OPAM version" && opam --version 
echo "Ocaml version" && ocaml -version

# opam packages!
# This doesn't work with opam 1.2.2
# opam install -q -y --unlock-base $OPAMPKGS

# planout
if [[ ! -e planout ]]; then 
    git clone https://github.com/facebook/planout.git
fi

Z3_PATH="z3-4.6.0-x64-ubuntu-14.04"
# z3
if [[ ! -e ${Z3_PATH}.zip ]]; then
    wget https://github.com/Z3Prover/z3/releases/download/z3-4.6.0/${Z3_PATH}.zip
    unzip ${Z3_PATH}.zip
fi
export PATH=$PATH:"$(pwd)/${Z3_PATH}/bin"
echo "Z3 version" && z3 --version

# package dependencies
for pkg in $OPAMPKGS; do
#    opam install -q -y --unlock-base $pkg
    opam install -q -y $pkg
done
