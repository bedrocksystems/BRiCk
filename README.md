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

- LLVM 17 or greater (we've tested against 17 and 18)
- cmake
- [opam 2](https://opam.ocaml.org/)

### Native dependencies: Linux (Ubuntu)

```sh
# install opam and cmake
sudo apt install cmake opam
# install llvm 18 (see directions here: https://apt.llvm.org/)
wget https://apt.llvm.org/llvm.sh
chmod +x llvm.sh
sudo ./llvm.sh 18 all
```

### Native dependencies: OSX

For OSX we recommend clang 18:

```sh
brew install llvm@18 cmake opam
export PATH=/usr/local/opt/llvm@18/bin:${PATH}
```

### Setup

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
```

### Building

Building is primarily done via [dune](https://github.com/ocaml/dune) and can be done using

```sh
$ dune build
```

## Examples
See the examples in the `tests` directory to get an idea of coverage that the logic supports.
More examples will be added as the feature set evolves.

You can run the tests with:

```sh
$ dune test
```

You can run `cpp2v` on your own files by invoking

```sh
$ dune exec cpp2v -- ...cpp2v options... -- ...clang options...
```

## Repository Layout

- `src` and `include` -- the implementation of the `cpp2v` tool.
  - `llvm-include` -- extensions of LLVM source code (see `llvm-include/LICENSE.txt` for the license of these files)
- `coq-upoly` -- universe polymorphic monad libraries
- `theories` -- the core Coq development.
  - `prelude` -- BlueRock's prelude extending [stdpp](https://gitlab.mpi-sws.org/iris/stdpp)
  - `lang/cpp` -- the C++ syntax and semantics
    - `syntax` -- the definition of the C++ AST (abstract syntax tree)
    - `semantics` -- core semantic definitions that are independent of separation logic
    - `logic` -- the separation logic weakest pre-condition semantics
    - `parser` -- the environment used to interpret the generated code.

## Coq IDEs

The following command can be used to create a `_CoqProject` file for use by Coq IDEs.
```sh
$ ln -s _CoqProject.template _CoqProject
```
