CPPS=A.cpp B.cpp
HPPS=A.hpp
VS=$(patsubst %.cpp,%_cpp.v,$(CPPS)) $(patsubst %.hpp,%_hpp.v,$(HPPS))
VOS=$(patsubst %.v,%.vo,$(VS))

coq: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

clean:
	@ rm $(VS) $(VOS)

A_cpp.v: A.cpp
	./../cpp2v $< > $@
A_hpp.v: A.hpp
	./../cpp2v $< > $@
B_cpp.v: B.cpp
	./../cpp2v $< > $@

%.o: %.cpp
	gcc -c $<

Makefile.coq: $(VS)
	coq_makefile -f _CoqProject > Makefile.coq
