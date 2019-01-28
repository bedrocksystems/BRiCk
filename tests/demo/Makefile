CPPS=A.cpp B.cpp
HPPS=A.hpp
VS=$(patsubst %.cpp,%_cpp.v,$(CPPS)) $(patsubst %.hpp,%_hpp.v,$(HPPS))
VOS=$(patsubst %.v,%.vo,$(VS))

coq: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

clean:
	@ rm $(VS) $(VOS)

%_cpp.v: %.cpp
	./../cpp2v $< -- > $@
%_hpp.v: %.hpp
	./../cpp2v $< -- > $@

%.o: %.cpp
	gcc -c $<

Makefile.coq: $(VS)
	coq_makefile -f _CoqProject -o Makefile.coq
