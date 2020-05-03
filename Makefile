#
# Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
default_target: coq

COQPATHFILE=$(wildcard _CoqPath)
COQMAKEFILE=$(COQBIN)coq_makefile

EXTRA_DIR=coqdocjs/extra
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS


cpp2v: build/Makefile
	$(MAKE) -C build cpp2v

cpp2v_plugin: build/Makefile
	$(MAKE) -C build cpp2v_plugin

all: coq cpp2v test

coq: Makefile.coq
	$(MAKE) -f Makefile.coq
	mkdir -p build/
	rm -f build/bedrock
	ln -s `pwd`/theories build/bedrock

doc: coq
	rm -rf public
	rm -rf html
	$(MAKE) -f Makefile.coq html
	$(MAKE) -C doc html
	cp -r doc/html/* html/
	cp -r $(EXTRA_DIR)/resources/* html
	cp html/toc.html html/index.html

doc_extra:
	git clone --depth 1 https://github.com/coq-community/coqdocjs.git doc_extra

html: doc
public: html doc_extra
	mv html public

release: coq cpp2v cpp2v_plugin
	rm -rf cpp2v
	mkdir cpp2v
	cp build/libcpp2v_plugin.so cpp2v
	cp build/cpp2v cpp2v
	cp -r theories cpp2v/bedrock

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	$(MAKE) -C doc clean

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

test: test-cpp2v

test-plugin: build-minimal cpp2v_plugin
	$(MAKE) -C tests/plugin

test-cpp2v: build-minimal cpp2v
	CPP2V=`pwd`/build/cpp2v $(MAKE) -C cpp2v-tests

build-minimal: Makefile.coq
	$(MAKE) -f Makefile.coq theories/lang/cpp/parser.vo
	mkdir -p build/
	rm -f build/bedrock
	ln -s `pwd`/theories build/bedrock

.PHONY: test install coq all doc html clean install cpp2v cpp2v_plugin

build/Makefile:
	mkdir -p build
	(cd build; cmake ..)

touch_deps:
	touch `find -iname *.vo`  || true
	touch `find -iname *.vok` || true
	touch `find -iname *.vos` || true
	touch `find -iname *.glob` || true
	touch `find -iname *.aux` || true
	touch `find tests/cpp2v-parser/ -iname *.v` || true
	touch `find build` || true

deps.pdf: _CoqProject
	coqdep -f _CoqProject -dumpgraphbox deps.dot > /dev/null
	dot -Tpdf -o deps.pdf deps.dot

.PHONY: touch_deps
