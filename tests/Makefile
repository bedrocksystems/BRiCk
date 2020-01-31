#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
all: cpp2v-parser includes local-scope class value-cat io alloc constants lock simple # list

cpp2v-parser:
	$(MAKE) -C cpp2v-parser

includes:
	$(MAKE) -C includes

local-scope:
	$(MAKE) -C local-scope

value-cat:
	$(MAKE) -C value-cat

class:
	$(MAKE) -C class

io:
	$(MAKE) -C io

alloc:
	$(MAKE) -C alloc

list:
	$(MAKE) -C list

lock:
	$(MAKE) -C lock

plugin:
	$(MAKE) -C plugin

constants:
	$(MAKE) -C constants

.PHONY: cpp2v-parser includes local-scope class value-cat io alloc list clean lock plugin constants

clean:
	$(MAKE) -C cpp2v-parser clean
	$(MAKE) -C includes clean
	$(MAKE) -C local-scope clean
	$(MAKE) -C value-cat clean
	$(MAKE) -C class clean
	$(MAKE) -C io clean
	$(MAKE) -C alloc clean
	$(MAKE) -C lock clean
	$(MAKE) -C plugin clean
	$(MAKE) -C constants clean
