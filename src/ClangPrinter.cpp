/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 */
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>

#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"

using namespace clang;

ClangPrinter::ClangPrinter(clang::ASTContext *context)
    : context_(context), engine_(IntrusiveRefCntPtr<DiagnosticIDs>(),
                                 IntrusiveRefCntPtr<DiagnosticOptions>()) {
    mangleContext_ = ItaniumMangleContext::create(*context, engine_);
}

unsigned
ClangPrinter::getTypeSize(const BuiltinType *t) const {
    return this->context_->getTypeSize(t);
}

void
ClangPrinter::printGlobalName(const NamedDecl *decl, CoqPrinter &print,
                              bool raw) {
    if (!raw) {
        print.output() << "\"";
    }
    if (auto fd = dyn_cast<FunctionDecl>(decl)) {
        if (fd->getLanguageLinkage() == LanguageLinkage::CLanguageLinkage) {
            print.output() << fd->getNameAsString();
        } else {
            mangleContext_->mangleCXXName(decl, print.output().nobreak());
        }
    } else {
        mangleContext_->mangleCXXName(decl, print.output().nobreak());
    }
    if (!raw) {
        print.output() << "\"";
    }
}

void
ClangPrinter::printName(const NamedDecl *decl, CoqPrinter &print) {
    if (decl->getDeclContext()->isFunctionOrMethod()) {
        print.ctor("Lname", false);
        print.output() << fmt::nbsp << "\"" << decl->getNameAsString() << "\"";
    } else {
        print.ctor("Gname", false);
        printGlobalName(decl, print);
    }
    print.output() << fmt::rparen;
}

void
ClangPrinter::printValCat(const Expr *d, CoqPrinter &print) {
#ifdef DEBUG
    d->dump(llvm::errs());
    llvm::errs().flush();
#endif
    // note(gmm): Classify doesn't work on dependent types which occur in templates
    // that clang can't completely eliminate.

    auto Class = d->Classify(*this->context_);
    if (Class.isLValue()) {
        print.output() << "Lvalue";
    } else if (Class.isXValue()) {
        print.output() << "Xvalue";
    } else if (Class.isRValue()) {
        print.output() << "Rvalue";
    } else {
        assert(false);
        //fatal("unknown value category");
    }
}

void
ClangPrinter::printExprAndValCat(const Expr *d, CoqPrinter &print) {
    auto depth = print.output().get_depth();
    print.output() << fmt::lparen;
    printValCat(d, print);
    print.output() << "," << fmt::nbsp;
    printExpr(d, print);
    print.output() << fmt::rparen;
    assert(depth == print.output().get_depth());
}

void
ClangPrinter::printField(const ValueDecl *decl, CoqPrinter &print) {
    if (const FieldDecl *f = dyn_cast<clang::FieldDecl>(decl)) {
        print.ctor("Build_field", false);
        this->printGlobalName(f->getParent(), print);
        print.output() << fmt::nbsp;

        if (decl->getName() == "") {
            const CXXRecordDecl *rd = f->getType()->getAsCXXRecordDecl();
            assert(rd && "unnamed field must be a record");
            print.ctor("Nanon", false);
            this->printGlobalName(rd, print);
            print.end_ctor();
        } else {
            print.str(decl->getName());
        }
        print.end_ctor();
    } else if (const CXXMethodDecl *meth =
                   dyn_cast<clang::CXXMethodDecl>(decl)) {
        print.ctor("Build_field", false);
        this->printGlobalName(meth->getParent(), print);
        print.output() << fmt::nbsp << "\""
                       << decl->getNameAsString() << "\"";
        print.end_ctor();
    } else if (const VarDecl *var = dyn_cast<VarDecl>(decl)) {

    } else {
        using namespace logging;
        fatal() << "member not pointing to field " << decl->getDeclKindName()
                << " (at " << sourceRange(decl->getSourceRange()) << ")\n";
        die();
    }
}

std::string
ClangPrinter::sourceRange(const SourceRange &&sr) const {
    return sr.printToString(this->context_->getSourceManager());
}
