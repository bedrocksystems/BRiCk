/*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
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
    : compiler_(compiler), context_(context) {
    mangleContext_ =
        ItaniumMangleContext::create(*context, compiler->getDiagnostics());
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

// #define CLANG_NAMES
#ifdef CLANG_NAMES
void
ClangPrinter::printTypeName(const TypeDecl *decl, CoqPrinter &print) const {
    std::string sout;
    llvm::raw_string_ostream out(sout);
    mangleContext_->mangleTypeName(QualType(decl->getTypeForDecl(), 0), out);
    out.flush();
    assert(3 < sout.length() && "mangled string length is too small");
    assert(sout.substr(0, 4) == "_ZTS");
    sout = sout.substr(4, sout.length() - 4);
    print.output() << "\"_Z" << sout << "\"";
}
#else /* CLANG_NAMES */
namespace {
unsigned
getAnonymousIndex(const NamedDecl *here) {
    auto i = 0;
    for (auto x : here->getDeclContext()->decls()) {
        if (x == here)
            return i;
        if (auto ns = dyn_cast<NamespaceDecl>(x)) {
            if (ns->isAnonymousNamespace())
                ++i;
        } else if (auto r = dyn_cast<RecordDecl>(x)) {
            if (r->getIdentifier() == nullptr)
                ++i;
        } else if (auto e = dyn_cast<EnumDecl>(x)) {
            if (e->getIdentifier() == nullptr)
                ++i;
        }
    }
    logging::fatal()
        << "Failed to find anonymous declaration in its own [DeclContext].\n"
        << here->getQualifiedNameAsString() << "\n";
    logging::die();
}
} // namespace

#ifdef STRUCTURED_NAMES
void
ClangPrinter::printTypeName(const TypeDecl *here, CoqPrinter &print) const {
    if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(here)) {
        print.ctor("Tspecialize");
        printTypeName(ts->getSpecializedTemplate(), print);
        print.output() << fmt::nbsp;
        auto &&args = ts->getTemplateArgs();
        print.begin_list();
        for (auto i = 0; i < args.size(); ++i) {
            auto &&arg = args[i];
            switch (arg.getKind()) {
            case TemplateArgument::ArgKind::Type:
                printQualType(arg.getAsType(), print);
                break;
            case TemplateArgument::ArgKind::Expression:
                printExpr(arg.getAsExpr(), print);
                break;
            case TemplateArgument::ArgKind::Integral:
                print.output() << arg.getAsIntegral().toString(10);
                break;
            case TemplateArgument::ArgKind::NullPtr:
                print.output() << "Enullptr";
                break;
            default:
                print.output() << "<else>";
            }
            print.cons();
        }
        print.end_list();
        print.end_ctor();
        return;
    }

    auto print_parent = [&](const DeclContext *parent) {
        if (auto pnd = dyn_cast<NamedDecl>(parent)) {
            printTypeName(pnd, print);
            print.output() << fmt::nbsp;
        } else {
            llvm::errs() << here->getDeclKindName() << "\n";
            assert(false && "unknown type in print_path");
        }
    };

    auto parent = here->getDeclContext();
    if (parent == nullptr or parent->isTranslationUnit()) {
        print.ctor("Qglobal", false);
        print.str(here->getName());
        print.end_ctor();
    } else if (auto nd = dyn_cast<NamespaceDecl>(here)) {
        print.ctor("Qnested", false);
        print_parent(parent);
        if (nd->isAnonymousNamespace() or nd->getIdentifier() == nullptr) {
            print.output() << "(Tanon " << getAnonymousIndex(nd) << ")";
        } else {
            print.str(here->getName());
        }
        print.end_ctor();
    } else if (auto rd = dyn_cast<RecordDecl>(here)) {
        print.ctor("Qnested", false);
        print_parent(parent);
        if (rd->getIdentifier() == nullptr) {
            print.output() << "(Tanon " << getAnonymousIndex(rd) << ")";
        } else {
            print.str(here->getName());
        }
        print.end_ctor();
    } else if (auto pnd = dyn_cast<NamedDecl>(parent)) {
        print.ctor("Qnested", false);
        printTypeName(pnd, print);
        print.output() << fmt::nbsp;
        print.str(here->getName());
        print.end_ctor();
    } else {
        llvm::errs() << here->getDeclKindName() << "\n";
        assert(false && "unknown type in print_path");
    }
}
#else  /* STRUCTURED NAMES */
// returns the number of components that it printed
size_t
printSimpleContext(const DeclContext *dc, CoqPrinter &print,
                   MangleContext &mangle, size_t remaining = 0) {
    if (dc == nullptr or dc->isTranslationUnit()) {
        print.output() << "_Z" << (1 < remaining ? "N" : "");
        return 0;
    } else if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(dc)) {
        if (auto dtor = ts->getDestructor()) {
            // HACK: this mangles an aggregate name by mangling
            // the destructor and then doing some string manipulation
            std::string sout;
            llvm::raw_string_ostream out(sout);
            mangle.mangleName(to_gd(dtor), out);
            out.flush();
            assert(3 < sout.length() && "mangled string length is too small");
            sout =
                sout.substr(0, sout.length() - 4); // cut off the final 'DnEv'
            if (not ts->getDeclContext()->isTranslationUnit() or
                0 < remaining) {
                print.output() << sout << (remaining == 0 ? "E" : "");
                return 2; // we approximate the whole string by 2
            } else {
                print.output() << "_Z" << sout.substr(3, sout.length() - 3);
                return 1;
            }
        } else {
            logging::debug()
                << "ClassTemplateSpecializationDecl not supported for "
                   "simple contexts.\n";
            ts->printName(logging::debug());
            logging::debug() << "\n";
            ts->printQualifiedName(print.output().nobreak());
            return true;
        }
    } else if (auto ns = dyn_cast<NamespaceDecl>(dc)) {
        auto parent = ns->getDeclContext();
        auto compound =
            printSimpleContext(parent, print, mangle, remaining + 1);
        if (not ns->isAnonymousNamespace()) {
            auto name = ns->getNameAsString();
            print.output() << name.length() << name;
        } else if (not ns->decls_empty()) {
            // a proposed scheme is to use the name of the first declaration.
            print.output() << ".<TODO>";
            // TODO
            // ns->field_begin()->printName(print.output().nobreak());
        } else {
            print.output() << "~<empty>";
        }
        if (remaining == 0 && 0 < compound)
            print.output() << "E";
        return compound + 1;
    } else if (auto rd = dyn_cast<RecordDecl>(dc)) {
        // NOTE: this occurs when you have a forward declaration,
        // e.g. [struct C;], or when you have a compiler builtin.
        // We need to mangle the name, but we can't really get any help
        // from clang.

        auto parent = rd->getDeclContext();
        auto compound =
            printSimpleContext(parent, print, mangle, remaining + 1);
        if (rd->getIdentifier()) {
            auto name = rd->getNameAsString();
            print.output() << name.length() << name;
        } else if (auto tdn = rd->getTypedefNameForAnonDecl()) {
            auto s = tdn->getNameAsString();
            print.output() << s.length() << s;
            //tdn->printName(print.output().nobreak());
        } else if (not rd->field_empty()) {
            print.output() << ".";
            rd->field_begin()->printName(print.output().nobreak());
        } else {
            assert(false);
        }
        if (remaining == 0 && 0 < compound)
            print.output() << "E";
        return compound + 1;
    } else if (auto ed = dyn_cast<EnumDecl>(dc)) {
        auto parent = ed->getDeclContext();
        auto compound =
            printSimpleContext(parent, print, mangle, remaining + 1);
        if (ed->getIdentifier()) {
            auto name = ed->getNameAsString();
            print.output() << name.length() << name;
            //} else if (auto tdn = rd->getTypedefNameForAnonDecl()) {
            //    llvm::errs() << "typedef name not null " << tdn << "\n";
            //    tdn->printName(print.output().nobreak());
        } else {
            if (ed->enumerators().empty()) {
                // no idea what to do
                print.output() << "<empty-enum>";
            } else {
                print.output() << ".";
                ed->enumerators().begin()->printName(print.output().nobreak());
            }
        }
        if (remaining == 0 && 0 < compound)
            print.output() << "E";
        return compound + 1;
    } else if (auto fd = dyn_cast<FunctionDecl>(dc)) {
        std::string sout;
        llvm::raw_string_ostream out(sout);
        mangle.mangleName(to_gd(fd), out);
        out.flush();
        assert(3 < sout.length() && "mangled string length is too small");
        if (not fd->getDeclContext()->isTranslationUnit()) {
            print.output() << sout << (remaining == 0 ? "E" : "");
            return 2; // we approximate the whole string by 2
        } else {
            print.output() << sout;
            return 1;
        }
    } else {
        logging::fatal() << "Unknown type (" << dc->getDeclKindName()
                         << ") in [printSimpleContext]\n";
        logging::die();
    }
}

void
ClangPrinter::printTypeName(const TypeDecl *decl, CoqPrinter &print) const {
    if (auto RD = dyn_cast<CXXRecordDecl>(decl)) {
        print.output() << "\"";
        printSimpleContext(RD, print, *mangleContext_);
        print.output() << "\"";
    } else if (auto rd = dyn_cast<RecordDecl>(decl)) {
        // NOTE: this only matches C records, not C++ records
        // therefore, we do not perform any mangling.
        logging::debug() << "RecordDecl: " << decl->getQualifiedNameAsString()
                         << "\n";
        print.output() << "\"";
        decl->printQualifiedName(print.output().nobreak());
        print.output() << "\"";
    } else if (auto ed = dyn_cast<EnumDecl>(decl)) {
        print.output() << "\"";
        printSimpleContext(ed, print, *mangleContext_);
        print.output() << "\"";
    } else {
        using namespace logging;
        fatal() << "Unknown decl kind to [printTypeName]: "
                << decl->getQualifiedNameAsString() << " "
                << decl->getDeclKindName() << "\n";
        die();
    }
}
#endif /* STRUCTURED_NAMES */
#endif /* CLANG_NAMES */

void
ClangPrinter::printObjName(const ValueDecl *decl, CoqPrinter &print, bool raw) {
    assert(!raw && "printing raw object names is no longer supported");

    // All enumerations introduce types, but only some of them have names.
    // While positional names work in scoped contexts, they generally
    // do not work in extensible contexts (e.g. the global context)
    //
    // To address this, we use the name of their first declation.
    // To avoid potential clashes (since the first declaration might be
    // a term name and not a type name), we prefix the symbol with a dot,
    // e.g.
    // [enum { X , Y , Z };] -> [.X]
    // note that [MangleContext::mangleTypeName] does *not* follow this
    // strategy.

    if (auto ecd = dyn_cast<EnumConstantDecl>(decl)) {
        // While they are values, they are not mangled because they do
        // not end up in the resulting binary. Therefore, we need a special
        // case.
        auto ed = dyn_cast<EnumDecl>(ecd->getDeclContext());
        print.ctor("Cenum_const", false);
        printTypeName(ed, print);
        print.output() << " \"";
        ecd->printName(print.output().nobreak());
        print.output() << "\"";
        print.end_ctor();
#if 0
        } else {
            assert(not ed->enumerators().empty());
            auto i = *ed->enumerators().begin();
            print.output() << "\"\" (* ";
            printTypeName(ed, print);
            ed->print.output() << " / " << ed->getNameAsString() << " *)";
            //print.ctor("Cenum_const", false);

#if 0
            auto parent = ed->getDeclContext();
            while (not(parent == nullptr or parent->isTranslationUnit())) {
                if (auto td = dyn_cast<TypeDecl>(parent)) {
                    print.ctor("Cenum_const", false);
                    printTypeName(td, print); // TODO this is wrong.
                    print.output() << " \"";
                    ecd->printName(print.output().nobreak());
                    print.output() << "\"";
                    print.end_ctor();
                    return;
                } else if (auto ns = dyn_cast<NamespaceDecl>(parent)) {
                    if (ns->isAnonymousNamespace()) {
                        parent = ns->getDeclContext();
                        continue;
                    }
                    print.output() << "\"";
                    ns->printQualifiedName(print.output().nobreak());
                    print.output() << "\"";
                    break;
                }
            }
            print.output() << "\"";
            ecd->printName(print.output().nobreak());
            print.output() << "\"";
#endif
        }
#endif
    } else if (mangleContext_->shouldMangleDeclName(decl)) {
        print.output() << "\"";
        mangleContext_->mangleName(to_gd(decl), print.output().nobreak());
        print.output() << "\"";
    } else {
        print.output() << "\"";
        decl->printQualifiedName(print.output().nobreak());
        print.output() << "\"";
    }
}

namespace {
Optional<int>
getParameterNumber(const ParmVarDecl *decl) {
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
} // namespace

void
ClangPrinter::printParamName(const ParmVarDecl *decl, CoqPrinter &print) const {
    print.output() << "\"";
    if (decl->getIdentifier()) {
        decl->printName(print.output().nobreak());
    } else {
        auto d = dyn_cast<ParmVarDecl>(decl);
        auto i = getParameterNumber(d);
        if (i.hasValue()) {
            print.output() << "#" << i;
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
