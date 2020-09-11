#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	@ $(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f *_names.v *_hpp.v *_cpp.v *_c.v *_h.v

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq
