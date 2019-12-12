h[![pipeline status](https://gitlab.com/bedrocksystems/cpp2v/badges/master/pipeline.svg)](https://gitlab.com/bedrocksystems/cpp2v/commits/master)


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
-Xclang -plugin-arg-cpp2v -Xclang -names -Xclang -plugin-arg-cpp2v -Xclang foo_ames_cpp.v ...standard clang options...
```

## Build & Dependenies

### TL;DR Linux (Ubuntu)

The following script should work, but you can customize it based on what you have:

```sh
sudo apt install llvm-8 llvm-8-dev clang-8 libclang-8-dev cmake opam
# install opam dependencies
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin coq 8.9.1
opam install coq coq-charge-core coq-ltac-iter
# install iris
git clone https://gitlab.mpi-sws.org/iris/iris.git
(cd iris; git reset --hard b958d569; make build-dep; make -j3; make install)
# install cpp2v
git clone https://github.com/bedrocksystems/cpp2v.git
(cd cpp2v; make cpp2v coq)
```

### TL;DR OSX

```sh
brew install llvm cmake opam
export PATH=/usr/local/opt/llvm/bin:${PATH}
# install opam dependencies
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin coq 8.9.1
opam install coq coq-charge-core coq-ltac-iter
# install iris
git clone https://gitlab.mpi-sws.org/iris/iris.git
(cd iris; git reset --hard b958d569; make build-dep; make -j3; make install)
# install cpp2v
git clone https://github.com/bedrocksystems/cpp2v.git
cd cpp2v
mkdir build && cd build
cmake -D CMAKE_EXE_LINKER_FLAGS=-L/usr/local/opt/llvm/lib ..
cmake --build .
cd ..
make cpp2v coq
```

## Long Version

This repository is broken down into two components. The `cpp2v` tool does not require Coq, and the Coq libraries do not require `cpp2v`. However, the two components are coupled because they operate on the same underlying syntax.

### The cpp2v Tool

To install the `cpp2v` tool, you need the following packages (they can be installed via `apt` on a Ubuntu distribution).

1. `llvm-8`, `llvm-8-dev`, `clang-8`, `libclang-8-dev`
2. `cmake`

#### OSX Instructions

On an OSX system, you run the following commands.

```sh
$ brew install llvm cmake
$ export PATH=/usr/local/opt/llvm/bin:${PATH}
```

### Coq
You can get all of the Coq dependencies via `opam` with the following command.

```shell
$ opam install coq coq-charge-core coq-ltac-iter
```

See [`opam` installation instructions](http://coq-blog.clarus.me/use-opam-for-coq.html) for help installing opam in Linux.

Note that you probably need to pin Coq to 8.9.1 as that is the currently supported version.

To install Iris:

```sh
# install Iris
$ opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
$ git clone https://gitlab.mpi-sws.org/iris/iris.git; cd iris; git reset --hard b958d569; make build-dep; make -j3
$ make install
```

#### OSX Instructions

On OSX, `opam` can be installed via `brew`.

```sh
$ brew install opam
$ opam repo add coq-released https://coq.inria.fr/opam/released
```

More detailed code for building.

```sh
$ brew install llvm cmake
$ export PATH=/usr/local/opt/llvm/bin:${PATH}
$ git clone https://github.com/bedrocksystems/cpp2v.git
$ cd cpp2v
$ mkdir build && cd build
$ cmake -D CMAKE_EXE_LINKER_FLAGS=-L/usr/local/opt/llvm/lib ..
$ cmake --build .
```

## Building
You can build `cpp2v` using the following commands.

```sh
$ make cpp2v cpp2v_plugin
```

You can build the Coq development using (this is the default):

```sh
$ make coq
```

You can run the tests with

```sh
$ make test
```

## Examples
See the examples in the `tests` directory.
More examples will be added as the feature set evolves.

## Repository Layout

- The implementation of the `cpp2v` tool is in `src` and `include`.
- The definition of the accompanying Coq data types is in `theories/Syntax` directory. The notation in `theories/Parser.v` is used to setup the environment for the generated code.
- The axiomatic semantics of the abstract syntax tree is defined in the `theories/Sem` directory.
- Some *basic* automation is included in `theories/Auto/`
