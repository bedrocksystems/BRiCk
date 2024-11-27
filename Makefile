#
# Copyright (c) 2019-2024 BedRock Systems, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source
# License. See the LICENSE-BedRock file in the repository root for details.
#

# You can override this with a different program which you can use to preview
# html files within your filesystem.
DOCOPEN ?= xdg-open

all:
	dune build @default @runtest
.PHONY: all

_CoqProject: _CoqProject.template
	@cp $< $@

SHELL := /bin/bash

BUILD_ROOT=../../_build/default/fmdeps/cpp2v-core
COQDOC_DIR=doc/sphinx/_static/coqdoc
COQLIB=${PWD}/../../_build/install/default/lib/coq

doc:
	@dune clean
	@dune build
	#@dune build @../coq/install
	@rm -rf /tmp/coqdocjs
	@cp -r coqdocjs /tmp
	@rm -rf doc/sphinx/_static/coqdoc
	@mkdir -p doc/sphinx/_static/css/coqdocjs doc/sphinx/_static/js/coqdocjs
	@cp -r coqdocjs/extra/resources/*.css doc/sphinx/_static/css/coqdocjs
	@cp -r coqdocjs/extra/resources/*.js doc/sphinx/_static/js/coqdocjs
	@COQLIB=${COQLIB} dune build --cache=disabled @doc
	@mkdir -p ${COQDOC_DIR}
	@cp -r -t ${COQDOC_DIR} $$(find ${BUILD_ROOT} -type d -name '*.html')
	+@$(MAKE) -C doc html
.PHONY: doc

doc-open: doc
	$(DOCOPEN) doc/sphinx/_build/html/index.html
.PHONY: doc-open

doc-clean:
	+@$(MAKE) -C doc clean
.PHONY: doc-clean

clean: doc-clean
	@dune clean || echo "dune not found; not cleaning dune-generated documentation files"
	@rm -f _CoqProject
.PHONY: clean
