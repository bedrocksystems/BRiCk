CS=$(wildcard *.c)
CPPS=$(wildcard *.cpp)
HS=$(wildcard *.h)
HPPS=$(wildcard *.hpp)
VS=$(patsubst %.cpp,%_cpp.v,$(CPPS)) $(patsubst %.hpp,%_hpp.v,$(HPPS)) $(patsubst %.c,%_c.v,$(CS)) $(patsubst %.h,%_h.v,$(HS))
VOS=$(patsubst %.v,%.vo,$(VS))

coq: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

clean:
	@ rm $(VS) $(VOS)


%_c.v: %.c
	./../cpp2v $< -- > $@
%_h.v: %.h
	./../cpp2v $< -- > $@
%_cpp.v: %.cpp
	./../cpp2v $< -- > $@
%_hpp.v: %.hpp
	./../cpp2v $< -- > $@

%.o: %.cpp
	gcc -c $<

Makefile.coq: $(VS)
	coq_makefile -f _CoqProject -o Makefile.coq
