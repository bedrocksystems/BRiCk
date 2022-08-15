#!/bin/sh
# Temporary workaround for FM-2813; will be fixed better with FM-2681
set -ex
brick_path=fmdeps/cpp2v-core
cp ${brick_path}/dune-ci/root-dune-project dune-project
cp ${brick_path}/dune-ci/root-dune dune
mkdir -p support/fm/
cp ${brick_path}/dune-ci/coqc_timing.sh support/fm/coqc_timing.sh
ln -sf ${brick_path}/coq-cpp2v-bin.opam coq-cpp2v-bin.opam
