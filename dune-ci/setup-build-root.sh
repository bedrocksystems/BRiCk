#!/bin/sh
# We simulate a dune project composition to work around https://github.com/ocaml/dune/issues/6005.
set -ex
brick_path=fmdeps/cpp2v-core
cp ${brick_path}/dune-ci/root-dune-project dune-project
