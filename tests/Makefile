all: cpp2v-parser demo local-scope class value-cat c-test

cpp2v-parser:
	(cd cpp2v-parser; ./test-all.sh)

demo:
	$(MAKE) -C demo

local-scope:
	$(MAKE) -C local-scope

value-cat:
	$(MAKE) -C value-cat

class:
	$(MAKE) -C class

c-test:
	$(MAKE) -C c-test

.PHONY: cpp2v-parser demo local-scope class value-cat c-test
