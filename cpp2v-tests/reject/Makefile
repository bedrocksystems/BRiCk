#
# Copyright (c) 2020 BedRock Systems, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
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
