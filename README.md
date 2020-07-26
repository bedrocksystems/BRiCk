[![pipeline status](https://gitlab.com/bedrocksystems/cpp2v/badges/master/pipeline.svg)](https://gitlab.com/bedrocksystems/cpp2v/commits/master)


# cpp2v

Tool for converting C++ files into Coq files.

## Running

### As a standalone tool

```sh
cpp2v -v -names XXX_names.v -o XXX_cpp.v XXX.cpp -- ...clang options...
```

### As a plugin

```sh
CPP2V_PLUGIN=./libcpp2v_plugin.so	# .dylib on OSX
clang -Xclang -load -Xclang $CPP2V_PLUGIN -Xclang -plugin -Xclang cpp2v -Xclang -plugin-arg-cpp2v -Xclang -o -Xclang -plugin-arg-cpp2v -Xclang foo_cpp.v
-Xclang -plugin-arg-cpp2v -Xclang -names -Xclang -plugin-arg-cpp2v -Xclang foo_names_cpp.v ...standard clang options...
```

## Build & Dependencies

The following scripts should work, but you can customize them based on your
needs.
They must be run inside a clone of this repository.

Our instructions are for Linux (Ubuntu) and OSX.

### Coq dependencies

Install [opam 2](https://opam.ocaml.org/), for instance with `sudo apt install
opam` or `brew install opam`.

Then:
```sh
# install opam dependencies
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin -n coq 8.11.0
opam install -j3 coq coq-ext-lib coq-lens coq-iris.dev.2020-07-04.0.e2639ac1
```

### Linux (Ubuntu)

```sh
sudo apt install llvm-9 llvm-9-dev clang-9 libclang-9-dev cmake
# install cpp2v-core
make coq cpp2v && make install
# to build the cpp2v-core plugin, do:
make plugin
```

### OSX

```sh
brew install llvm cmake opam zlib
export PATH=/usr/local/opt/llvm/bin:${PATH}
# install cpp2v-core
make coq cpp2v && make install
# to build the cpp2v-core plugin, do:
make plugin
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
