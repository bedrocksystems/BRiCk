#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	@ $(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f *_names.v *_hpp.v *_cpp.v *_c.v *_h.v

Makefile.coq: $(VS)
	coq_makefile -f _CoqProject -o Makefile.coq
