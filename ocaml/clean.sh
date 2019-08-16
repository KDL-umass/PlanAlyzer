#!/bin/bash

# Remove the Oasis-generated files
rm -rf setup.ml setup.data setup.log myocamlbuild.ml Makefile configure
rm -rf _tags _build

# Remove libraries
rm -rf planalyzer/annotations/META
rm -rf planalyzer/annotations/annotations.mllib
rm -rf planalyzer/annotations/annotations.mldylib

rm -rf planalyzer/corepo/META
rm -rf planalyzer/corepo/corepo.mllib
rm -rf planalyzer/corepo/corepo.mldylib

rm -rf planalyzer/estimators/META
rm -rf planalyzer/estimators/estimators.mllib
rm -rf planalyzer/estimators/estimators.mldylib

rm -rf planalyzer/graphs/META
rm -rf planalyzer/graphs/graphs.mllib
rm -rf planalyzer/graphs/graphs.mldylib

rm -rf planalyzer/oratio/META
rm -rf planalyzer/oratio/oratio.mllib
rm -rf planalyzer/oratio/oratio.mldylib

rm -rf planalyzer/planout/META
rm -rf planalyzer/planout/planout.mllib
rm -rf planalyzer/planout/planout.mldylib

rm -rf planalyzer/utils/META
rm -rf planalyzer/utils/utils.mllib
rm -rf planalyzer/utils/utils.mldylib

rm -rf planalyzer/META
rm -rf planalyzer/targets.mllib
rm -rf planalyzer/targets.mldylib

# R-rf emove binaries
rm -rf *.byte
rm -rf *.native
