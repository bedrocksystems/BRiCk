/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License. 
 * See the LICENSE-BedRock file in the repository root for details. 
 */
#pragma once

#include <optional>

namespace clang {
class TranslationUnitDecl;
}

class CoqPrinter;

namespace clang {
class CompilerInstance;
}

using namespace clang;

class ToCoqConsumer : public clang::ASTConsumer {
public:
    explicit ToCoqConsumer(clang::CompilerInstance* compiler,
                           const Optional<std::string> output_file,
                           const Optional<std::string> spec_file,
                           const Optional<std::string> notations_file)
        : compiler_(compiler),
          spec_file_(spec_file), output_file_(output_file),
          notations_file_(notations_file) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        toCoqModule(&Context, Context.getTranslationUnitDecl());
    }

private:
    void toCoqModule(clang::ASTContext *ctxt,
                     clang::TranslationUnitDecl *decl);

private:
    clang::CompilerInstance*    compiler_;
    const Optional<std::string> spec_file_;
    const Optional<std::string> output_file_;
    const Optional<std::string> notations_file_;
};
