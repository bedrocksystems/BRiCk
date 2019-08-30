#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
CS=$(wildcard *.c)
HS=$(wildcard *.h)
CPPS=$(wildcard *.cpp)
HPPS=$(wildcard *.hpp)
CPP2V?=$(abspath $(lastword $(MAKEFILE_LIST)))/../build/cpp2v

VS=$(patsubst %.h,%_h.v,$(HS)) $(patsubst %.hpp,%_hpp.v,$(HPPS)) $(patsubst %.c,%_c.v,$(CS)) $(patsubst %.cpp,%_cpp.v,$(CPPS))
VOS=$(patsubst %.v,%.vo,$(VS))

CFLAGS=

coq: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

clean:
	@ rm $(VS) -rf $(VOS)

%_c.v: %.c $(CPP2V)
	$(CPP2V) -o $@ $< -- $(CFLAGS)
%_h.v: %.h $(CPP2V)
	$(CPP2V) -o $@ $< -- $(CFLAGS)
%_cpp.v: %.cpp $(CPP2V)
	$(CPP2V) -o $@ $< -- $(CFLAGS)
%_hpp.v: %.hpp $(CPP2V)
	$(CPP2V) -o $@ $< -- $(CFLAGS)

%_c_spec.v: %.c $(CPP2V)
	$(CPP2V) -spec $@ $< -- $(CFLAGS)
%_h_spec.v: %.h $(CPP2V)
	$(CPP2V) -spec $@ $< -- $(CFLAGS)
%_cpp_spec.v: %.cpp $(CPP2V)
	$(CPP2V) -spec $@ $< -- $(CFLAGS)
%_hpp_spec.v: %.hpp $(CPP2V)
	$(CPP2V) -spec $@ $< -- $(CFLAGS)

%.o: %.cpp
	gcc -c $<

Makefile.coq: $(VS)
	coq_makefile -f _CoqProject -o Makefile.coq
