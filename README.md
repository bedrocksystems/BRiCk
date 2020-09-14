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

- LLVM 10
- cmake
- [opam 2](https://opam.ocaml.org/)

### Native dependencies: Linux (Ubuntu)

```sh
sudo apt install llvm-10-dev clang-tools-10 libclang-10-dev cmake
sudo apt install opam
```

### Native dependencies: OSX


```sh
brew install llvm cmake opam
export PATH=/usr/local/opt/llvm/bin:${PATH}
```

### Build

The script below uses 4 cores, customize as needed.
```sh
# install opam dependencies
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
# install cpp2v Coq library and Coq dependencies
opam pin -n coq 8.11.2
opam pin -n coq-cpp2v .
opam install coq coq-cpp2v
# install cpp2v binary
opam pin coq-cpp2v-bin .
```

If you want to build the cpp2v-core plugin, do:
```
make -j4 plugin
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
