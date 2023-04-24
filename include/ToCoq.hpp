/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include <clang/AST/ASTConsumer.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/ASTMutationListener.h>
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

class ToCoqConsumer : public clang::ASTConsumer, clang::ASTMutationListener {
public:
    explicit ToCoqConsumer(clang::CompilerInstance *compiler,
                           const std::optional<std::string> output_file,
                           const std::optional<std::string> notations_file,
                           const std::optional<std::string> templates_file,
                           bool elaborate = true)
        : compiler_(compiler), output_file_(output_file),
          notations_file_(notations_file), templates_file_(templates_file),
          elaborate_(elaborate) {}

public:
    // Implementation of `clang::ASTConsumer`
    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        toCoqModule(&Context, Context.getTranslationUnitDecl());
    }

    virtual void HandleTagDeclDefinition(TagDecl *decl) override;
    virtual bool HandleTopLevelDecl(DeclGroupRef decl) override;
    virtual void HandleInlineFunctionDefinition(FunctionDecl *decl) override;
    virtual void
    HandleCXXImplicitFunctionInstantiation(FunctionDecl *decl) override;
    virtual ASTMutationListener *GetASTMutationListener() override {
        return this;
    }

public:
    // Implementation of clang::ASTMutationListener
    virtual void
    AddedCXXTemplateSpecialization(const ClassTemplateDecl *TD,
                                   const ClassTemplateSpecializationDecl *D) {
        // TODO [const_cast] is a code-smell.
        // The implementation calls this method from a non-`const` method.
        // it is not clear why this method should take a
        // `const ClassTemplateSpecializationDecl` rather than a non-`const`
        // See question: https://stackoverflow.com/questions/76085015/using-clangs-astconsumer-to-force-generation-of-implicit-members
        elab(const_cast<ClassTemplateSpecializationDecl *>(D), true);
    }

private:
    void toCoqModule(clang::ASTContext *ctxt, clang::TranslationUnitDecl *decl);
    void elab(Decl *, bool = false);

private:
    clang::CompilerInstance *compiler_;
    const std::optional<std::string> output_file_;
    const std::optional<std::string> notations_file_;
    const std::optional<std::string> templates_file_;
    bool elaborate_;
};
