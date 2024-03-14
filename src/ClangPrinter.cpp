/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
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
#include <clang/Frontend/CompilerInstance.h>
#include <optional>

using namespace clang;

ClangPrinter::ClangPrinter(clang::CompilerInstance *compiler,
                           clang::ASTContext *context, Trace::Mask trace)
    : compiler_(compiler), context_(context), trace_(trace) {
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

fmt::Formatter&
ClangPrinter::printParamName(const ParmVarDecl *decl, CoqPrinter &print) {
    if (trace(Trace::Name)) trace("printParamName", loc::of(decl));

    print.output() << "\"";
    if (decl->getIdentifier()) {
        decl->printName(print.output().nobreak());
    } else {
        auto d = dyn_cast<ParmVarDecl>(decl);
        auto i = getParameterNumber(d);
        if (i.has_value()) {
            print.output() << "#" << i.value();
        } else {
            auto loc = loc::of(decl);
            error_prefix(logging::fatal(), loc)
                << "error: cannot find parameter\n";
            debug_dump(loc);
            logging::die();
        }
    }
    return print.output() << "\"";
}

fmt::Formatter&
ClangPrinter::printValCat(const Expr *d, CoqPrinter &print) {
    if (trace(Trace::Type)) trace("printValCat", loc::of(d));

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
            auto loc = loc::of(d);
            error_prefix(logging::fatal(), loc)
                << "error: cannot determine value category\n";
            debug_dump(loc);
            logging::die();
        }
        return print.output();
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
    return print.output();
}

fmt::Formatter&
ClangPrinter::printNameForAnonTemplateParam(unsigned depth, unsigned index,
                                            CoqPrinter &print, loc::loc loc) {
    if (trace(Trace::Name)) trace("printNameForAnonTemplateParam", loc);
    for (auto d = decl_; d; d = d->getLexicalParent()) {
        if (auto psd = dyn_cast<ClassTemplatePartialSpecializationDecl>(d)) {
            for (auto i : psd->getTemplateParameters()->asArray()) {
                if (auto tpd = dyn_cast<TemplateTypeParmDecl>(i)) {
                    if (tpd->getDepth() != depth)
                        break;
                    if (tpd->getIndex() == index)
                        return print.str(tpd->getName());
                }
            }
        } else if (auto fd = dyn_cast<FunctionDecl>(d)) {
            if (auto x = fd->getDescribedTemplateParams())
                for (auto i : x->asArray()) {
                    if (auto tpd = dyn_cast<TemplateTypeParmDecl>(i)) {
                        if (tpd->getDepth() != depth)
                            break;
                        if (tpd->getIndex() == index)
                            return print.str(tpd->getName());
                    }
                }
        }
    }
    error_prefix(logging::debug(), loc)
        << "error: could not infer template parameter name at depth "
        << depth << ", index " << index << "\n";
    debug_dump(loc);
    logging::die();
}

fmt::Formatter&
ClangPrinter::printField(const ValueDecl *decl, CoqPrinter &print) {
    if (trace(Trace::Decl)) trace("printField", loc::of(decl));

    if (const FieldDecl *f = dyn_cast<clang::FieldDecl>(decl)) {
        print.ctor("Build_field", false);
        this->printTypeName(f->getParent(), print, loc::of(f));
        print.output() << fmt::nbsp;

        if (decl->getName() == "") {
            const CXXRecordDecl *rd = f->getType()->getAsCXXRecordDecl();
            assert(rd && "unnamed field must be a record");
            print.ctor("Nanon", false);
            this->printTypeName(rd, print, loc::of(f));
            print.end_ctor();
        } else {
            print.str(decl->getName());
        }
        print.end_ctor();
    } else if (const CXXMethodDecl *meth =
                   dyn_cast<clang::CXXMethodDecl>(decl)) {
        print.ctor("Build_field", false);
        this->printTypeName(meth->getParent(), print, loc::of(meth));
        print.output() << fmt::nbsp << "\"" << decl->getNameAsString() << "\"";
        print.end_ctor();
    } else if (isa<VarDecl>(decl)) {

    } else {
        auto loc = loc::of(decl);
        error_prefix(logging::fatal(), loc)
            << "error: member not pointing to field\n";
        debug_dump(loc);
        logging::die();
    }
    return print.output();
}

std::string
ClangPrinter::sourceLocation(const SourceLocation loc) const {
    return loc.printToString(this->context_->getSourceManager());
}

std::string
ClangPrinter::sourceRange(const SourceRange sr) const {
    return sr.printToString(this->context_->getSourceManager());
}

const Decl*
ClangPrinter::getDecl() const {
    return decl_ ? Decl::castFromDeclContext(decl_) : nullptr;
}

llvm::raw_ostream&
ClangPrinter::debug_dump(loc::loc loc) {
    return logging::debug() << loc::dump(loc, getContext(), getDecl());
}

llvm::raw_ostream&
ClangPrinter::error_prefix(llvm::raw_ostream& os, loc::loc loc) {
    return os << loc::prefix(loc, getContext(), getDecl());
}

llvm::raw_ostream&
ClangPrinter::trace(StringRef whence, loc::loc loc) {
    auto& os = llvm::errs();
    os << "[TRACE] " << whence;
    auto decl = getDecl();
    if (loc::can_trace(loc, decl))
        os << " " << loc::trace(loc, getContext(), decl);
    return os << "\n";
}

fmt::Formatter&
ClangPrinter::printVariadic(bool va, CoqPrinter &print) const {
    return print.output() << (va ? "Ar_Variadic" : "Ar_Definite");
}

fmt::Formatter&
ClangPrinter::printCallingConv(clang::CallingConv cc, CoqPrinter &print, loc::loc loc) {
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
        error_prefix(logging::fatal(), loc)
            << "error: unsupported calling convention\n";
        debug_dump(loc);
        logging::die();
    }
    return print.output();
}
