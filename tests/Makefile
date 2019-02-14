all: cpp2v-parser demo local-scope class

cpp2v-parser:
	(cd cpp2v-parser; ./test-all.sh)

demo:
	$(MAKE) -C demo

local-scope:
	$(MAKE) -C local-scope

class:
	$(MAKE) -C class

.PHONY: cpp2v-parser demo local-scope class
