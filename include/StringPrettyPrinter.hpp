/*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

#pragma once

#include "CoqPrinter.hpp"
#include <clang/AST/Expr.h>
void string_pretty_print(const clang::StringLiteral* lit, CoqPrinter& print);
