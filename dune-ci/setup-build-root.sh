#!/bin/sh
set -ex
brick_path=fmdeps/cpp2v-core
cp ${brick_path}/dune-ci/root-dune-project dune-project
ln -sf ${brick_path}/coq-cpp2v-bin.opam coq-cpp2v-bin.opam
