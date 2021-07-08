/*
 * Copyright (c) 2020 BedRock Systems, Inc.
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

using namespace clang;

ClangPrinter::ClangPrinter(clang::CompilerInstance *compiler,
                           clang::ASTContext *context)
    : compiler_(compiler), context_(context) /*,
      engine_(IntrusiveRefCntPtr<DiagnosticIDs>(),
              IntrusiveRefCntPtr<DiagnosticOptions>()) */
{
    mangleContext_ =
        ItaniumMangleContext::create(*context, compiler->getDiagnostics());
}

clang::Sema &
ClangPrinter::getSema() const {
    return this->compiler_->getSema();
}

unsigned
ClangPrinter::getTypeSize(const BuiltinType *t) const {
    return this->context_->getTypeSize(t);
}

#if CLANG_VERSION_MAJOR >= 11
static GlobalDecl
to_gd(const NamedDecl *decl) {
    if (auto ct = dyn_cast<CXXConstructorDecl>(decl)) {
        return GlobalDecl(ct, CXXCtorType::Ctor_Complete);
    } else if (auto dt = dyn_cast<CXXDestructorDecl>(decl)) {
        return GlobalDecl(dt, CXXDtorType::Dtor_Deleting);
    } else {
        return GlobalDecl(decl);
    }
}
#else
static const NamedDecl *
to_gd(const NamedDecl *decl) {
    return decl;
}
#endif /* CLANG_VERSION_MAJOR >= 11 */

void
ClangPrinter::printTypeName(const NamedDecl *decl, CoqPrinter &print) {
    printObjName(decl, print);
}

void
ClangPrinter::printObjName(const NamedDecl *decl, CoqPrinter &print, bool raw) {
    if (!raw) {
        print.output() << "\"";
    }

    if (isa<RecordDecl>(decl)) {
        if (auto RD = dyn_cast<CXXRecordDecl>(decl)) {
            auto dtor = RD->getDestructor();
            std::string sout;
            llvm::raw_string_ostream out(sout);
            mangleContext_->mangleName(to_gd(dtor), out);
            print.output() << sout.substr(3, sout.length() - 7);
        } else {
            assert(false);
        }
#if 0
        decl->getNameForDiagnostic(print.output().nobreak(),
                                   PrintingPolicy(getContext().getLangOpts()),
                                   true);
#endif
    } else if (mangleContext_->shouldMangleDeclName(decl)) {
#if 0
        auto x = to_gd(decl);
        assert(decl == x.getDecl() && "HERE");
        auto y = cast<NamedDecl>(x.getDecl());
        auto DC = y->getDeclContext();
        llvm::errs() << "DC = " << isa<CapturedDecl>(DC)
                     << isa<OMPDeclareReductionDecl>(DC)
                     << isa<OMPDeclareMapperDecl>(DC) << "\n";
        DC->getRedeclContext()->dumpDeclContext();
        llvm::errs() << "===========\n";
        if (dyn_cast<clang::BlockDecl, clang::Decl const>(y)) {
            assert(false && "HERE 2");
        }
#endif
        mangleContext_->mangleName(to_gd(decl), print.output().nobreak());
    } else {
        print.output() << decl->getQualifiedNameAsString();
#if 0
        if (auto fd = dyn_cast<FunctionDecl>(decl)) {
            if (fd->getLanguageLinkage() == LanguageLinkage::CLanguageLinkage) {
                print.output() << fd->getNameAsString();
            } else {
                mangleContext_->mangleName(to_gd(fd), print.output().nobreak());
            }
        } else {
            mangleContext_->mangleName(to_gd(decl), print.output().nobreak());
        }
#endif
    }

    if (!raw) {
        print.output() << "\"";
    }
}

Optional<int>
ClangPrinter::getParameterNumber(const ParmVarDecl *decl) {
    assert(decl->getDeclContext()->isFunctionOrMethod() &&
           "function or method");
    if (auto fd = dyn_cast_or_null<FunctionDecl>(decl->getDeclContext())) {
        int i = 0;
        for (auto p : fd->parameters()) {
            if (p == decl)
                return Optional<int>(i);
            ++i;
        }
        llvm::errs() << "failed to find parameter\n";
    }
    return Optional<int>();
}

void
ClangPrinter::printParamName(const ParmVarDecl *decl, CoqPrinter &print) {
    auto name = decl->getIdentifier();
    print.output() << "\"";
    if (name == nullptr) {
        auto d = dyn_cast<ParmVarDecl>(decl);
        auto i = getParameterNumber(d);
        if (i.hasValue()) {
            print.output() << "#" << i;
        }
    } else {
        print.output() << name;
    }
    print.output() << "\"";
}

void
ClangPrinter::printName(const NamedDecl *decl, CoqPrinter &print) {
    if (decl->getDeclContext()->isFunctionOrMethod()) {
        print.ctor("Lname", false) << fmt::nbsp;
        auto name = decl->getNameAsString();
        if (auto pd = dyn_cast_or_null<ParmVarDecl>(decl)) {
            printParamName(pd, print);
        } else {
            print.output() << "\"" << decl->getNameAsString() << "\"";
        }
    } else {
        print.ctor("Gname", false);
        printObjName(decl, print);
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
    } else if (Class.isPRValue()) {
        print.output() << "Prvalue";
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
ClangPrinter::printExprAndValCat(const Expr *d, CoqPrinter &print,
                                 OpaqueNames &li) {
    auto depth = print.output().get_depth();
    print.output() << fmt::lparen;
    printValCat(d, print);
    print.output() << "," << fmt::nbsp;
    printExpr(d, print, li);
    print.output() << fmt::rparen;
    assert(depth == print.output().get_depth());
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
        print.output() << fmt::nbsp << "\"" << decl->getNameAsString() << "\"";
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
ClangPrinter::sourceRange(const SourceRange sr) const {
    return sr.printToString(this->context_->getSourceManager());
}

void
ClangPrinter::printCallingConv(clang::CallingConv cc, CoqPrinter &print) {
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
