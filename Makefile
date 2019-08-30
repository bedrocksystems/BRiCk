#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
default_target: coq

COQPATHFILE=$(wildcard _CoqPath)
COQMAKEFILE=$(COQBIN)coq_makefile

bin: build/Makefile
	$(MAKE) -C build

all: coq bin test

coq: Makefile.coq
	$(MAKE) -f Makefile.coq
	mkdir -p build/
	rm -rf build/Cpp
	cp -r theories/ build/Cpp

doc: coq
	$(MAKE) -f Makefile.coq html
html: doc

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

test: coq bin
	$(MAKE) -C tests

.PHONY: test install coq all doc html clean install

build/Makefile:
	mkdir -p build
	(cd build; cmake ..)
