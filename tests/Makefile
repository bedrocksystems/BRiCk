default_target: coq
.PHONY: default_target

COQMAKEFILE=$(COQBIN)coq_makefile

coq: Makefile.coq
	+$(MAKE) -f Makefile.coq
.PHONY: coq

Makefile.coq Makefile.coq.conf: _CoqProject.template Makefile
	+$(COQMAKEFILE) -f _CoqProject.template -o Makefile.coq
