#
# Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#

COQMAKEFILE=$(COQBIN)coq_makefile

COQMK := $(MAKE) -f Makefile.coq

ROOT=$(shell (cd .. &&pwd))
include ./Makefile.doc
COQDOCFLAGS += --external https://bedrocksystems.gitlab.io/cpp2v bedrock
export COQDOCFLAGS

coq: Makefile.coq
	+@$(COQMK)
.PHONY: coq

doc: coq
	+@$(COQMK) html
.PHONY: doc

html: doc
.PHONY: html

clean:
	+@if test -f Makefile.coq; then $(COQMK) cleanall; fi
	rm -f Makefile.coq Makefile.coq.conf
.PHONY: clean

Makefile.coq Makefile.coq.conf: _CoqProject Makefile
	+$(COQMAKEFILE) -f _CoqProject -o Makefile.coq
