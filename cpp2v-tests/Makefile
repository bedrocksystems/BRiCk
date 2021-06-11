#
# Copyright (C) BedRock Systems Inc. 2019-2020
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#
COQC	?= coqc
QPATH   ?= ../theories
WARN    ?= -w -notation-overridden
CPP2V	?= ../build/cpp2v
CPPFLAGS = -std=c++17

ALL	= $(wildcard *.cpp)

all: $(ALL:%.cpp=%_cpp.vo) $(ALL:%.cpp=%_cpp_names.vo) reject
.PHONY: all

ast: $(ALL:%.cpp=%_cpp.v) $(ALL:%.cpp=%_cpp_names.v)
.PHONY: ast

clean:
	rm -f *.v *.vo *.vok *.vos *.glob *.aux .*.aux
	$(MAKE) -C reject clean
.PHONY: clean

%_cpp.v %_cpp_names.v: %.cpp $(CPP2V)
	$(CPP2V) -v -names $*_cpp_names.v -o $*_cpp.v $< -- $(CPPFLAGS)

%.vo: %.v
	$(COQC) $(WARN) -Q $(QPATH) bedrock $<

.PRECIOUS: %_cpp.v

reject:
	+$(MAKE) -C reject
.PHONY: reject
