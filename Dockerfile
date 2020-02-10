######################################################
# Dockerfile for the bedrocksystems/cpp2v CI/CD image
# See https://gitlab.com/help/user/packages/container_registry/index
# for details.
# TL;DR:
#   0. Set up a personal access token with "api" scope at
#      gitlab.com->User Settings->Access Tokens. For security,
#      set an expiration date on the token (e.g., "tomorrow").
#
#   1. Log in to the Gitlab Container Registry using the
#      personal access token by doing:
#
#        cd cpp2v
#        docker login registry.gitlab.com/bedrocksystems/cpp2v -u <gitlab-username> -p <access-token>
#
#   2. Build the docker image on your local machine:
#
#        docker build -t registry.gitlab.com/bedrocksystems/cpp2v/<image-name> .
#
#   3. Deploy the docker image to the Gitlab registry:
#
#        docker push registry.gitlab.com/bedrocksystems/cpp2v/<image-name>
######################################################

FROM ocaml/opam2:debian-unstable

ENV NJOBS=2
ENV COMPILER="4.06"
ENV CAMLP5_VER="7.05"
ENV FINDLIB_VER="1.8.0"
ENV COQ_VER="8.9.1"
ENV LLVM_MAJ_VER="9"

RUN sudo apt-get update -y
RUN sudo apt-get install -y m4 cmake llvm-${LLVM_MAJ_VER} libllvm${LLVM_MAJ_VER} llvm-${LLVM_MAJ_VER}-dev llvm-${LLVM_MAJ_VER}-runtime clang-${LLVM_MAJ_VER} clang-tools-${LLVM_MAJ_VER} libclang-common-${LLVM_MAJ_VER}-dev libclang-${LLVM_MAJ_VER}-dev libclang1-${LLVM_MAJ_VER}
RUN opam init -j ${NJOBS} -n -y --compiler=$COMPILER
RUN opam switch set ${COMPILER}
RUN eval $(opam config env)
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam config list
RUN opam update
RUN opam repo add coq-released https://coq.inria.fr/opam/released || echo "coq-released registered"
RUN opam install -j ${NJOBS} -y coq.${COQ_VER} coq-ltac-iter coq-ext-lib
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
RUN git clone https://gitlab.mpi-sws.org/iris/iris.git; cd iris; git reset --hard b958d569; eval $(opam config env); make build-dep; make -j3; make install
RUN sudo apt-get install time