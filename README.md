# BRiCk

A program logic for verifying concurrent C++ in Coq.

## Running

### As a standalone tool

```sh
cpp2v -v -names XXX_names.v -o XXX_cpp.v XXX.cpp -- ...clang options...
```

## Build & Dependencies

The following scripts should work, but you can customize them based on your
needs.
They must be run inside a clone of this repository.

Our instructions are for Linux (Ubuntu) and OSX.

- LLVM 15 (should be backwards compatibile with 10 & 11 & ... & 14)
- cmake
- [opam 2](https://opam.ocaml.org/)

### Native dependencies: Linux (Ubuntu)

```sh
# For Ubuntu 22.04 LTS:
sudo apt install llvm-14 llvm-14-dev clang-14 libclang-14-dev libclang-cpp14-dev
# For Ubuntu 22.10 (tested 1 Nov 2022):
sudo apt install llvm-15 llvm-15-dev clang-15 libclang-15-dev libclang-cpp15-dev mlir-15-tools libmlir-15-dev clang-tools-15 clang-tidy-15 clangd-15
sudo apt install cmake opam
```

### Native dependencies: OSX

For OSX we recommend clang 11 due to issues linking with clang 12:

```sh
brew install llvm@11 cmake opam
export PATH=/usr/local/opt/llvm@11/bin:${PATH}
```

### Build

The script below uses 4 cores, customize as needed.
```sh
# install opam dependencies
eval $(opam env)
# The first time, run:
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
# install cpp2v Coq library and Coq dependencies
opam update
opam pin -n coq-cpp2v .
opam pin -n coq-cpp2v-bin .
opam install coq coq-cpp2v coq-cpp2v-bin
# install cpp2v binary
```

If you want to build the documentation locally, do:
```
git submodule init
git submodule update
```

## Examples
See the examples in the `tests` directory.
More examples will be added as the feature set evolves.

You can run the tests with:

```sh
$ make test
```

## Repository Layout

- The implementation of the `cpp2v` tool is in `src` and `include`.
- The definition of the accompanying Coq data types is in `theories/lang/cpp/syntax` directory. The notation in `theories/lang/cpp/parser.v` is used to setup the environment for the generated code.
- The axiomatic semantics of the abstract syntax tree is defined in the `theories/lang/cpp/logic` directory.

## Coq IDEs

The following command creates a `_CoqProject` file for use by Coq IDEs.
```sh
$ ln -s _CoqProject.template _CoqProject
```
