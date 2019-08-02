#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier:AGPL-3.0-or-later
#
CPP2V?=$(shell which cpp2v)

CFLAGS=

%_c.v: %.c $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CFLAGS)
%_h.v: %.h $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CFLAGS)
%_cpp.v: %.cpp $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CFLAGS)
%_hpp.v: %.hpp $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CFLAGS)

ifdef DEBUG
%_c_spec.v: %.c $(CPP2V)
	$(CPP2V) -v -spec $@ $< -- $(CFLAGS)
	@ echo $@
	@ cat $@
%_h_spec.v: %.h $(CPP2V)
	$(CPP2V) -v -spec $@ $< -- $(CFLAGS)
	@ echo $@
	@ cat $@
%_cpp_spec.v: %.cpp $(CPP2V)
	$(CPP2V) -v -spec $@ $< -- $(CFLAGS)
	@ echo $@
	@ cat $@
%_hpp_spec.v: %.hpp $(CPP2V)
	$(CPP2V) -v -spec $@ $< -- $(CFLAGS)
	@ echo $@
	@ cat $@
else
%_c_spec.v: %.c $(CPP2V)
	$(CPP2V) -v -spec $@ $< -- $(CFLAGS)
%_h_spec.v: %.h $(CPP2V)
	$(CPP2V) -v -spec $@ $< -- $(CFLAGS)
%_cpp_spec.v: %.cpp $(CPP2V)
	$(CPP2V) -v -spec $@ $< -- $(CFLAGS)
%_hpp_spec.v: %.hpp $(CPP2V)
	$(CPP2V) -v -spec $@ $< -- $(CFLAGS)
endif
