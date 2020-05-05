#
# Copyright (C) BedRock Systems Inc. 2019
#
# SPDX-License-Identifier:MIT-0
#
CPP2V_PLUGIN ?= ../build/libcpp2v_plugin.so
LOAD_PLUGIN=-Xclang -load -Xclang $(CPP2V_PLUGIN) -Xclang -add-plugin -Xclang cpp2v
OUT_OPTION=-Xclang -plugin-arg-cpp2v -Xclang -o -Xclang -plugin-arg-cpp2v -Xclang
NAMES_OPTION=-Xclang -plugin-arg-cpp2v -Xclang -names -Xclang -plugin-arg-cpp2v -Xclang

QPATH ?= ../theories
COQARGS=-Q $(QPATH) bedrock

all: demo_cpp.v demo_cpp.vo demo_cpp_names.vo

config:
	@ echo $(CPP2V_PATH)

demo_cpp.v demo.o demo_cpp_names.v: demo.cpp $(CPP2V_PLUGIN)
	clang++ $(LOAD_PLUGIN) $(OUT_OPTION) demo_cpp.v $(NAMES_OPTION) demo_cpp_names.v $< -c

demo_cpp.vo: demo_cpp.v
	coqc $(COQARGS) demo_cpp.v

demo_cpp_names.vo: demo_cpp_names.v
	coqc $(COQARGS) demo_cpp_names.v

clean:
	rm -f *.vo *.vok *.vos *_names.v *_cpp.v *.o *.glob
