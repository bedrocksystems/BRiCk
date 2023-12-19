/*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>
#include <clang/Basic/Version.h>
#include <clang/Frontend/CompilerInstance.h>
#include <optional>

using namespace clang;

ClangPrinter::ClangPrinter(clang::CompilerInstance *compiler,
                           clang::ASTContext *context)
    : compiler_(compiler), context_(context) {
    mangleContext_ =
        ItaniumMangleContext::create(*context, compiler->getDiagnostics());
}

unsigned
ClangPrinter::getTypeSize(const BuiltinType *t) const {
    return this->context_->getTypeSize(t);
}

namespace {
std::optional<int>
getParameterNumber(const ParmVarDecl *decl) {
    assert(decl->getDeclContext()->isFunctionOrMethod() &&
           "function or method");
    if (auto fd = dyn_cast_or_null<FunctionDecl>(decl->getDeclContext())) {
        int i = 0;
        for (auto p : fd->parameters()) {
            if (p == decl)
                return std::optional<int>(i);
            ++i;
        }
        llvm::errs() << "failed to find parameter\n";
    }
    return std::optional<int>();
}
} // namespace

void
ClangPrinter::printDeclName(const NamedDecl* decl, CoqPrinter& print) const {
    print.output() << '"';
    decl->printName(print.output().nobreak());
    print.output() << '"';
}

void
ClangPrinter::printParamName(const ParmVarDecl *decl, CoqPrinter &print) const {
    print.output() << "\"";
    if (decl->getIdentifier()) {
        decl->printName(print.output().nobreak());
    } else {
        auto d = dyn_cast<ParmVarDecl>(decl);
        auto i = getParameterNumber(d);
        if (i.has_value()) {
            print.output() << "#" << i.value();
        } else {
            logging::fatal() << "failed to find a parameter.";
            logging::die();
        }
    }
    print.output() << "\"";
}

void
ClangPrinter::printValCat(const Expr *d, CoqPrinter &print) {
#ifdef DEBUG
    d->dump(llvm::errs());
    llvm::errs().flush();
#endif
    // note(gmm): Classify doesn't work on dependent types which occur in templates
    // that clang can't completely eliminate.

    if (print.templates()) {
        if (d->isLValue())
            print.output() << "Lvalue";
        else if (d->isPRValue())
            print.output() << "Prvalue";
        else if (d->isXValue())
            print.output() << "Xvalue";
        else {
            using namespace logging;
            fatal() << "Error: cannot determine value category"
                    << " (at " << sourceRange(d->getSourceRange()) << ")\n";
            die();
        }
        return;
    }

    auto Class = d->Classify(*this->context_);
    if (Class.isLValue()) {
        print.output() << "Lvalue";
    } else if (Class.isXValue()) {
        print.output() << "Xvalue";
    } else if (Class.isPRValue()) {
        print.output() << "Prvalue";
    } else {
        assert(false);
        //fatal("unknown value category");
    }
}

void
ClangPrinter::printInstantiatableRecordName(const RecordDecl *decl,
                                            CoqPrinter &print) {
    if (print.templates()) {
        printType(decl->getTypeForDecl(), print);
    } else {
        printTypeName(decl, print);
    }
}

void
ClangPrinter::printNameForAnonTemplateParam(unsigned depth, unsigned index,
                                            CoqPrinter &print) {
    for (auto d = decl_; d; d = d->getLexicalParent()) {
        if (auto psd = dyn_cast<ClassTemplatePartialSpecializationDecl>(d)) {
            for (auto i : psd->getTemplateParameters()->asArray()) {
                if (auto tpd = dyn_cast<TemplateTypeParmDecl>(i)) {
                    if (tpd->getDepth() != depth)
                        break;
                    if (tpd->getIndex() == index) {
                        print.str(tpd->getName());
                        return;
                    }
                }
            }
        } else if (auto fd = dyn_cast<FunctionDecl>(d)) {
            if (auto x = fd->getDescribedTemplateParams())
                for (auto i : x->asArray()) {
                    if (auto tpd = dyn_cast<TemplateTypeParmDecl>(i)) {
                        if (tpd->getDepth() != depth)
                            break;
                        if (tpd->getIndex() == index) {
                            print.str(tpd->getName());
                            return;
                        }
                    }
                }
        }
    }
    logging::debug() << "Could not find variable declaration " << depth << " "
                     << index << " in " << decl_;

    if (decl_) {
#if CLANG_VERSION_MAJOR > 15
        decl_->dumpAsDecl();
#endif
    }
    print.str("??TODO??");
}

void
ClangPrinter::printField(const ValueDecl *decl, CoqPrinter &print) {
    if (const FieldDecl *f = dyn_cast<clang::FieldDecl>(decl)) {
        print.ctor("Build_field", false);
        this->printTypeName(f->getParent(), print);
        print.output() << fmt::nbsp;

        if (decl->getName() == "") {
            const CXXRecordDecl *rd = f->getType()->getAsCXXRecordDecl();
            assert(rd && "unnamed field must be a record");
            print.ctor("Nanon", false);
            this->printTypeName(rd, print);
            print.end_ctor();
        } else {
            print.str(decl->getName());
        }
        print.end_ctor();
    } else if (const CXXMethodDecl *meth =
                   dyn_cast<clang::CXXMethodDecl>(decl)) {
        print.ctor("Build_field", false);
        this->printTypeName(meth->getParent(), print);
        print.output() << fmt::nbsp << "\"" << decl->getNameAsString() << "\"";
        print.end_ctor();
    } else if (isa<VarDecl>(decl)) {

    } else {
        using namespace logging;
        fatal() << "member not pointing to field " << decl->getDeclKindName()
                << " (at " << sourceRange(decl->getSourceRange()) << ")\n";
        die();
    }
}

std::string
ClangPrinter::sourceLocation(const SourceLocation loc) const {
    return loc.printToString(this->context_->getSourceManager());
}

std::string
ClangPrinter::sourceRange(const SourceRange sr) const {
    return sr.printToString(this->context_->getSourceManager());
}

void
ClangPrinter::printVariadic(bool va, CoqPrinter &print) const {
    print.output() << (va ? "Ar_Variadic" : "Ar_Definite");
}

void
ClangPrinter::printCallingConv(clang::CallingConv cc, CoqPrinter &print) const {
#define PRINT(x)                                                               \
    case CallingConv::x:                                                       \
        print.output() << #x;                                                  \
        break;
#define OVERRIDE(x, y)                                                         \
    case CallingConv::x:                                                       \
        print.output() << #y;                                                  \
        break;
    switch (cc) {
        PRINT(CC_C);
        OVERRIDE(CC_X86RegCall, CC_RegCall);
        OVERRIDE(CC_Win64, CC_MsAbi);
#if 0
        PRINT(CC_X86StdCall);
        PRINT(CC_X86FastCall);
        PRINT(CC_X86ThisCall);
        PRINT(CC_X86VectorCall);
        PRINT(CC_X86Pascal);
        PRINT(CC_X86_64SysV);
        PRINT(CC_AAPCS);
        PRINT(CC_AAPCS_VFP);
        PRINT(CC_IntelOclBicc);
        PRINT(CC_SpirFunction);
        PRINT(CC_OpenCLKernel);
        PRINT(CC_Swift);
        PRINT(CC_PreserveMost);
        PRINT(CC_PreserveAll);
        PRINT(CC_AArch64VectorCall);
#endif
    default:
        using namespace logging;
        logging::fatal() << "unsupported calling convention\n";
        logging::die();
    }
}
