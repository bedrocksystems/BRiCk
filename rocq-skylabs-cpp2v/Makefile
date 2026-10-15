#
# Copyright (c) 2019-2024 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source
# License. See the LICENSE-BedRock file in the repository root for details.
#

CMAKE ?= cmake
BUILD_DIR ?= build
BUILD_ARGS ?=
BUILD_TYPE ?= Release

# CMake caches the LLVM and Clang it finds, so pass them explicitly when set:
# otherwise an existing build directory keeps using the old toolchain.
CMAKE_DIRS = $(if $(LLVM_DIR),-DLLVM_DIR=$(LLVM_DIR)) $(if $(Clang_DIR),-DClang_DIR=$(Clang_DIR))

all: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v
.PHONY: cpp2v

# Reconfigure on every build (cheap and idempotent) so that changes to the
# variables above take effect.
$(BUILD_DIR)/Makefile: $(MAKEFILE_LIST) CMakeLists.txt FORCE
	@$(CMAKE) -B $(BUILD_DIR) $(BUILD_ARGS) $(CMAKE_DIRS) -DCMAKE_BUILD_TYPE=$(BUILD_TYPE)

FORCE:
.PHONY: FORCE

clean:
	@rm -rf $(BUILD_DIR)
.PHONY: clean
