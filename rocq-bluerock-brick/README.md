# BRiCk

A program logic for verifying concurrent C++ in Rocq.

## Build & Dependencies

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

Building is done via [dune](https://github.com/ocaml/dune) and can be done
using

```sh
$ dune build
```

## Examples

See the examples in the `tests` directory to get an idea of coverage that the
logic supports. More examples will be added as the feature set evolves.

You can run the tests with:
```sh
$ dune runtest
```

## Repository Layout

- `theories` -- the core Coq development.
  - `prelude` -- BlueRock's prelude extending [stdpp](https://gitlab.mpi-sws.org/iris/stdpp)
  - `lang/cpp` -- the C++ syntax and semantics
    - `syntax` -- the definition of the C++ AST (abstract syntax tree)
    - `semantics` -- core semantic definitions that are independent of separation logic
    - `logic` -- the separation logic weakest pre-condition semantics
    - `parser` -- the environment used to interpret the generated code.

## Coq IDEs

The following command can be used to create a `_CoqProject` file for use by
Coq IDEs.
```sh
$ (cd .. && make _CoqProject)
```
