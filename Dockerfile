FROM ocaml/opam2:debian-unstable

ENV NJOBS=2
ENV COMPILER="4.06"
ENV CAMLP5_VER="7.05"
ENV FINDLIB_VER="1.8.0"
ENV COQ_VER="8.9.1"

RUN sudo apt-get update -y
RUN sudo apt-get install -y m4 cmake llvm-8 libllvm8 llvm-8-dev llvm-8-runtime clang-8 clang-tools-8 libclang-common-8-dev libclang-8-dev libclang1-8
RUN opam init -j ${NJOBS} -n -y --compiler=$COMPILER
RUN opam switch set ${COMPILER}
RUN eval $(opam config env)
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam config list
RUN opam update
RUN opam repo add coq-released https://coq.inria.fr/opam/released || echo "coq-released registered"
RUN opam install -j ${NJOBS} -y coq.${COQ_VER} coq-charge-core.1.2.0 coq-ltac-iter
RUN opam list
