#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#

DIRS=includes local-scope class value-cat io alloc constants lock simple list

all: cpp2v-parser $(DIRS)

cpp2v-parser:
	$(MAKE) -C cpp2v-parser

$(DIRS):
	$(MAKE) -C $@

.PHONY: cpp2v-parser $(DIRS)

clean:
	$(MAKE) -C cpp2v-parser clean
	$(MAKE) -C includes clean
	$(MAKE) -C local-scope clean
	$(MAKE) -C class clean
	$(MAKE) -C value-cat clean
	$(MAKE) -C io clean
	$(MAKE) -C alloc clean
	$(MAKE) -C constants clean
	$(MAKE) -C lock clean
	$(MAKE) -C simple clean
