#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

doc: coq
	$(MAKE) -f Makefile.coq html
html: doc

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: test install coq all doc html clean install cpp2v cpp2v_plugin
