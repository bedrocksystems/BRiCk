#
# Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#

ROOT=$(shell (cd .. &&pwd))

doc:
	$(MAKE) -C old doc
.PHONY: doc

html: doc
.PHONY: html

clean:
	$(MAKE) -C old clean
.PHONY: clean
