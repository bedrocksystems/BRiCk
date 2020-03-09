#
# Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
default_target: coq

COQPATHFILE=$(wildcard _CoqPath)
COQMAKEFILE=$(COQBIN)coq_makefile

cpp2v: build/Makefile
	$(MAKE) -C build cpp2v

cpp2v_plugin: build/Makefile
	$(MAKE) -C build cpp2v_plugin

all: coq cpp2v test

coq: Makefile.coq
	$(MAKE) -f Makefile.coq
	mkdir -p build/
	rm -rf build/bedrock
	ln -s `pwd`/theories build/bedrock

doc: coq
	rm -rf public
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cd doc/; $(MAKE) html
	mv doc/html/*.html html/
	mv html/toc.html html/index.html

html: doc
public: html
	mv html public

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	$(MAKE) -C doc clean

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

test: coq cpp2v
	CPP2V=`pwd`/build/cpp2v $(MAKE) -C tests

test-plugin: build-minimal cpp2v_plugin
	$(MAKE) -C tests/plugin

test-cpp2v: build-minimal cpp2v
	$(MAKE) -C tests/cpp2v-parser

build-minimal: Makefile.coq
	$(MAKE) -f Makefile.coq theories/lang/cpp/parser.vo
	mkdir -p build/
	rm -rf build/bedrock
	ln -s `pwd`/theories build/bedrock

.PHONY: test install coq all doc html clean install cpp2v cpp2v_plugin

build/Makefile:
	mkdir -p build
	(cd build; cmake ..)

deps.pdf: _CoqProject
	coqdep -f _CoqProject -dumpgraphbox deps.dot > /dev/null
	dot -Tpdf -o deps.pdf deps.dot

.PHONY: deps.pdf
