[![pipeline status](https://gitlab.com/bedrocksystems/cpp2v/badges/master/pipeline.svg)](https://gitlab.com/bedrocksystems/cpp2v/commits/master)


# cpp2v

Tool for converting C++ files into Coq files.

## Running

### As a Plugin

```sh
-Xclang -load -Xclang ./libcpp2v_plugin.so
-Xclang -plugin -Xclang cpp2v
-Xclang -plugin-arg-cpp2v -Xclang -o
-Xclang -plugin-arg-cpp2v -Xclang foo_cpp.v
-Xclang -plugin-arg-cpp2v -Xclang -spec
-Xclang -plugin-arg-cpp2v -Xclang foo_spec_cpp.v
```

## Dependencies

### C++
You will need the following packages (they can be installed via `apt` on a ubuntu distribution).

1. `llvm-8`, `llvm-8-dev`, `clang-8`, `libclang-8-dev`
2. `cmake`

#### OSX Instructions

```sh
$ brew install llvm cmake
$ export PATH=/usr/local/opt/llvm/bin:${PATH}
```

Install the Coq dependencies.
```sh
$ opam install coq coq-charge-core coq-ltac-iter
```


### Coq
You can get all of the Coq dependencies via `opam` with the following command.

```shell
$ opam install coq coq-charge-core coq-ltac-iter
```

See [`opam` installation instructions](http://coq-blog.clarus.me/use-opam-for-coq.html) for help installing opam in Linux.

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
$ make bin
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
The implementation of the `cpp2v` tool is in `src` and `include`.
The definition of the accompanying Coq data types is in `theories/Syntax/Ast.v` (and `theories/Parser.v`).
The axiomatic semantics of the abstract syntax tree is defined in the `theories/Sem` directory.
Some *basic* automation is included in `theories/Auto.v`.
