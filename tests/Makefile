#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
all: cpp2v-parser demo local-scope class value-cat return-ref c-test alloc list plugin

cpp2v-parser:
	$(MAKE) -C cpp2v-parser

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

alloc:
	$(MAKE) -C alloc

return-ref:
	$(MAKE) -C return-ref

list:
	$(MAKE) -C list

lock:
	$(MAKE) -C lock

plugin:
	$(MAKE) -C plugin

.PHONY: cpp2v-parser demo local-scope class value-cat c-test alloc return-ref list clean lock plugin

clean:
	$(MAKE) -C cpp2v-parser clean
	$(MAKE) -C demo clean
	$(MAKE) -C local-scope clean
	$(MAKE) -C value-cat clean
	$(MAKE) -C class clean
	$(MAKE) -C c-test clean
	$(MAKE) -C alloc clean
	$(MAKE) -C return-ref clean
	$(MAKE) -C list clean
	$(MAKE) -C lock clean
	$(MAKE) -C plugin clean
