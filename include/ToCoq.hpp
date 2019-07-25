/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#pragma once

#include <optional>

namespace clang {
class TranslationUnitDecl;
}

class CoqPrinter;

using namespace clang;

class ToCoqConsumer : public clang::ASTConsumer {
public:
    explicit ToCoqConsumer(const Optional<std::string> output_file,
                           const Optional<std::string> spec_file)
        : spec_file_(spec_file), output_file_(output_file) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        toCoqModule(&Context, Context.getTranslationUnitDecl());
    }

private:
    void toCoqModule(clang::ASTContext *ctxt,
                     const clang::TranslationUnitDecl *decl);

private:
    const Optional<std::string> spec_file_;
    const Optional<std::string> output_file_;
};
