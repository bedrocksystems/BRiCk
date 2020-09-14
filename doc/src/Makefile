#
# Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#

DIRS=
TANGLE_DIRS = $(addprefix tangle-, $(DIRS))

all: $(DIRS)
tangle-all: $(DIRS) _downloads $(TANGLE_DIRS)

_DOWNLOADS_DIR:=_downloads
_DOWNLOADS_FILES:=coq.mk rules.mk
_downloads:
	mkdir -p $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel
	cp template/Makefile.toplevel $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel/Makefile
	cp $(_DOWNLOADS_FILES) $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel
	zip -rj $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel.zip $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel
	zip -r $(_DOWNLOADS_DIR)/cpp2v-core-docs-full.zip . -x "_downloads/*" "*/.*" "*/*.vo*" \
								"*/*.glob" "*/Makefile.coq" "*/Makefile.coq.conf"

$(DIRS):
	$(MAKE) -C $@ coq

$(TANGLE_DIRS):
	$(MAKE) -C $(subst tangle-,,$@) tangle

.PHONY: $(DIRS) $(TANGLE_DIRS)

clean:
	rm -rf _downloads/
	$(foreach d,$(DIRS), $(MAKE) -C $(d) clean;)
