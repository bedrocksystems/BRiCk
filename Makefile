default_target: all

COQPATHFILE=$(wildcard _CoqPath)
COQMAKEFILE=$(COQBIN)coq_makefile

all: Makefile.coq
	$(MAKE) -f Makefile.coq

doc: all
	$(MAKE) -f Makefile.coq html
html: doc

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq
