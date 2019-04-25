COQC=coqc
CPP2V=$(shell which cpp2v)
ALL=$(wildcard *.cpp)

all: $(ALL:%.cpp=%_cpp.vo)

%_cpp.v: %.cpp $(CPP2V)
	$(CPP2V) $< -- > $@

%.vo: %.v
	$(COQC) -Q ../../theories Cpp $<

clean:
	rm -f *.v *.vo

.PHONY: clean all

.PRECIOUS: %_cpp.v
