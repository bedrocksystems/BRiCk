#
# Copyright (C) BedRock Systems Inc. 2019-2020
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
COQC	?= coqc
QPATH   ?= ../theories
CPP2V	?= ../build/cpp2v

ALL	= $(wildcard *.cpp)

all: $(ALL:%.cpp=%_cpp.vo) $(ALL:%.cpp=%_cpp_names.vo)

%_cpp.v %_cpp_names.v: %.cpp $(CPP2V)
	$(CPP2V) -v -names $*_cpp_names.v -o $*_cpp.v $< --

%.vo: %.v
	$(COQC) -Q $(QPATH) bedrock $<

clean:
	rm -f *.v *.vo *.glob *.aux

.PHONY: clean all

.PRECIOUS: %_cpp.v
