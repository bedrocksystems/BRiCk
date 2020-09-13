#
# Copyright (C) BedRock Systems Inc. 2020
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#

CPP2V ?= ../../build/cpp2v

SRC	= $(wildcard *.cpp)

AST = $(SRC:%.cpp=%_cpp.v)
ERR = $(SRC:%.cpp=%.cpp.ERR)

all: $(ERR)
.PHONY: all

clean:
	rm -f $(AST) $(ERR)
.PHONY: clean

# Ensure cpp2v rejects some constructs.
# We could go further, requiring a particular error message.
%.cpp.ERR : %.cpp $(CPP2V) Makefile
	@echo REJECT $<
	@if $(CPP2V) -v -o $*_cpp.v $< -- 2>$*.cpp.ERR; then echo >&2 "Error: $(CPP2V) accepted $<"; exit 1; fi

.PRECIOUS: %_cpp.v
