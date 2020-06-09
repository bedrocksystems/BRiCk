/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 */
#include "Logging.hpp"
#include <llvm/Support/raw_ostream.h>

namespace logging {
static Level log_level = Level::NONE;

llvm::raw_ostream&
log(Level level) {
    if (level < log_level) {
        return llvm::errs();
    } else {
        return llvm::nulls();
    }
}

void
set_level(Level level) {
    log_level = level;
}

[[noreturn]] void
die() {
    llvm::outs().flush();
    llvm::errs().flush();
    exit(1);
}
}