#
# Copyright (C) BedRock Systems Inc. 2019
#
# SPDX-License-Identifier:MIT-0
#
LOAD_PLUGIN=-Xclang -load -Xclang ${CPP2V_PLUGIN} -Xclang -add-plugin -Xclang cpp2v
OUT_OPTION=-Xclang -plugin-arg-cpp2v -Xclang -o -Xclang -plugin-arg-cpp2v -Xclang
NAMES_OPTION=-Xclang -plugin-arg-cpp2v -Xclang -names -Xclang -plugin-arg-cpp2v -Xclang

COQARGS=-Q ../theories bedrock

all: demo_cpp.v demo_cpp.vo demo_cpp_names.vo

config:
	@ echo ${CPP2V_PATH}

demo_cpp.v demo.o demo_cpp_names.v: demo.cpp ${CPP2V_PLUGIN}
	clang++ ${LOAD_PLUGIN} ${OUT_OPTION} demo_cpp.v ${NAMES_OPTION} demo_cpp_names.v $< -c

demo_cpp.vo: demo_cpp.v
	coqc ${COQARGS} demo_cpp.v

demo_cpp_names.vo: demo_cpp_names.v
	coqc ${COQARGS} demo_cpp_names.v
