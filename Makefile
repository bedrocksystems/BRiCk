coq: Makefile.coq
	$(MAKE) -f Makefile.coq

test: coq
	$(MAKE) -C test-suite

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

clean:
	$(MAKE) -f Makefile.coq clean
	rm -rf Makefile.coq Makefile.coq.conf
