  $ . ../setup.sh
  $ find
  .
  ./dummy.opam
  ./Makefile
  ./src
  ./src/server
  ./src/server/br-config.toml
  ./src/server/server.cpp
  ./src/server/attic
  ./src/server/attic/todo.cpp
  ./src/server/attic/junk.cpp
  ./src/server/include
  ./src/server/include/server.hpp
  ./src/client
  ./src/client/br-config.toml
  ./src/client/client.cpp
  ./src/client/include
  ./src/client/include/client.hpp
  ./dune-project
  ./include
  ./include/util.hpp
  ./include/junk.hpp
  ./br-project.toml
  $ br gen --debug
  Changed directory to [$TESTCASE_ROOT].
  Initial directory was [.].
  File [src/server/server.cpp]:
   - coq_dirpath: my.project.src.server
   - clang_includes: ../../include, include
  Creating directory [src/server/proof/server_cpp].
  File [src/server/include/server.hpp]:
   - coq_dirpath: my.project.src.server.include
   - clang_includes: ../../../include, ../include
  Creating directory [src/server/include/proof/server_hpp].
  File [src/client/client.cpp]:
   - coq_dirpath: my.project.src.client
   - clang_includes: ../../include, include
  Creating directory [src/client/proof/client_cpp].
  File [src/client/include/client.hpp]:
   - coq_dirpath: my.project.src.client.include
   - clang_includes: ../../../include, ../include
  Creating directory [src/client/include/proof/client_hpp].
  File [include/util.hpp]:
   - coq_dirpath: my.project.include
   - clang_includes: ../include
  Creating directory [include/proof/util_hpp].
  $ find
  .
  ./dummy.opam
  ./Makefile
  ./src
  ./src/server
  ./src/server/proof
  ./src/server/proof/server_cpp
  ./src/server/proof/server_cpp/dune
  ./src/server/br-config.toml
  ./src/server/server.cpp
  ./src/server/attic
  ./src/server/attic/todo.cpp
  ./src/server/attic/junk.cpp
  ./src/server/include
  ./src/server/include/proof
  ./src/server/include/proof/server_hpp
  ./src/server/include/proof/server_hpp/dune
  ./src/server/include/server.hpp
  ./src/client
  ./src/client/proof
  ./src/client/proof/client_cpp
  ./src/client/proof/client_cpp/dune
  ./src/client/br-config.toml
  ./src/client/client.cpp
  ./src/client/include
  ./src/client/include/proof
  ./src/client/include/proof/client_hpp
  ./src/client/include/proof/client_hpp/dune
  ./src/client/include/client.hpp
  ./dune-project
  ./include
  ./include/util.hpp
  ./include/proof
  ./include/proof/util_hpp
  ./include/proof/util_hpp/dune
  ./include/junk.hpp
  ./br-project.toml
  $ dune build
  $ find _build/default -name "*.vo"
  _build/default/src/server/proof/server_cpp/code.vo
  _build/default/src/server/proof/server_cpp/names.vo
  _build/default/src/server/include/proof/server_hpp/code.vo
  _build/default/src/server/include/proof/server_hpp/names.vo
  _build/default/src/client/proof/client_cpp/code.vo
  _build/default/src/client/proof/client_cpp/names.vo
  _build/default/src/client/include/proof/client_hpp/code.vo
  _build/default/src/client/include/proof/client_hpp/names.vo
  _build/default/include/proof/util_hpp/code.vo
  _build/default/include/proof/util_hpp/names.vo
  $ cat src/client/proof/client_cpp/dune
  (include_subdirs qualified)
  (coq.theory
   (name my.project.src.client.client_cpp)
   (package dummy)
   (theories
    stdpp
    iris
    elpi
    elpi_elpi
    Lens
    bedrock.upoly
    bedrock.prelude
    bedrock.lang
    Equations))
  (rule
   (targets code.v names.v)
   (deps
    (:input ../../client.cpp)
    (glob_files_rec ../../../../include/*.hpp)
    (glob_files_rec ../../include/*.hpp))
   (action
    (run cpp2v -v %{input} -o code.v -names names.v --
     -I../../../../include
     -I../../include)))
