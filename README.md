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
clang -Xclang -load -Xclang ./libcpp2v_plugin.so -Xclang -plugin -Xclang cpp2v -Xclang -plugin-arg-cpp2v -Xclang -o -Xclang -plugin-arg-cpp2v -Xclang foo_cpp.v
-Xclang -plugin-arg-cpp2v -Xclang -names -Xclang -plugin-arg-cpp2v -Xclang foo_names_cpp.v ...standard clang options...
```

## Build & Dependencies

### Linux (Ubuntu)

The following script should work, but you can customize it based on what you have:

```sh
sudo apt install llvm-9 llvm-9-dev clang-9 libclang-9-dev cmake opam
# install opam dependencies
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin coq 8.11.0
opam install coq coq-ext-lib coq-metacoq-template
# install iris
git clone https://gitlab.mpi-sws.org/iris/iris.git
(cd iris && git reset --hard 62be0a86890dbbf0dd3e4fc09edaa6d0227baebd && make build-dep && make -j3 && make install)
# install cpp2v-core
make coq cpp2v && make install
# to build the cpp2v-core plugin, do:
make plugin
```

### OSX

```sh
brew install llvm cmake opam zlib
export PATH=/usr/local/opt/llvm/bin:${PATH}
# install opam dependencies
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin coq 8.11.0
opam install coq coq-ext-lib
# install iris
git clone https://gitlab.mpi-sws.org/iris/iris.git
(cd iris && git reset --hard 62be0a86890dbbf0dd3e4fc09edaa6d0227baebd && make build-dep && make -j3 && make install)
# install cpp2v
git clone https://gitlab.com/bedrocksystems/cpp2v.git
cd cpp2v
mkdir build && cd build
cmake -D'CMAKE_SHARED_LINKER_FLAGS=-L/usr/local/opt/llvm/lib -lclangSerialization -lclangASTMatchers -lclangSema -lclangAnalysis -lclangRewriteFrontend -lclangEdit -lclangParse -lclangFrontend -lclangBasic -lclangDriver -lclangAST -lclangLex -lz -lcurses' -DCMAKE_EXE_LINKER_FLAGS=-L/usr/local/opt/llvm/lib ..
cmake --build .
cd ..
make coq install
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
