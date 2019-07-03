all: Makefile.coq
	$(MAKE) -f Makefile.coq

test: all
	$(MAKE) -C test-suite

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean
	rm -rf Makefile.coq Makefile.coq.conf
