/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include <clang/AST/ASTConsumer.h>
#include <clang/AST/ASTContext.h>
#include <llvm/ADT/Optional.h>
#include <optional>
#include <string>

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
    explicit ToCoqConsumer(clang::CompilerInstance *compiler,
                           const llvm::Optional<std::string> output_file,
                           const llvm::Optional<std::string> notations_file,
                           const llvm::Optional<std::string> templates_file,
                           bool elaborate = true) :
        compiler_(compiler),
        output_file_(output_file),
        notations_file_(notations_file),
        templates_file_(templates_file),
        elaborate_(elaborate) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        toCoqModule(&Context, Context.getTranslationUnitDecl());
    }

private:
    void toCoqModule(clang::ASTContext *ctxt, clang::TranslationUnitDecl *decl);

private:
    clang::CompilerInstance *compiler_;
    const Optional<std::string> output_file_;
    const Optional<std::string> notations_file_;
    const Optional<std::string> templates_file_;
    bool elaborate_;
};
