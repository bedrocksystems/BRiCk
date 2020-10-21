/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/RecordLayout.h"
#include "clang/Basic/Builtins.h"

using namespace clang;

CallingConv
getCallingConv(const Type *type) {
    if (auto ft = dyn_cast_or_null<FunctionType>(type)) {
        return ft->getCallConv();
    } else if (auto at = dyn_cast_or_null<AttributedType>(type)) {
        return getCallingConv(at->getModifiedType().getTypePtr());
    } else {
        type->dump();
        assert(false && "FunctionDecl type is not FunctionType");
        LLVM_BUILTIN_UNREACHABLE;
    }
}

CallingConv
getCallingConv(const FunctionDecl *decl) {
    return getCallingConv(decl->getType().getTypePtr());
}

void
PrintBuiltin(Builtin::ID id, const ValueDecl *decl, CoqPrinter &print,
             ClangPrinter &cprint) {
    switch (id) {
#define CASEB(x)                                                               \
    case Builtin::BI__builtin_##x:                                             \
        print.output() << "Bin_" #x;                                           \
        break;
        CASEB(alloca)
        CASEB(alloca_with_align)
        CASEB(launder)
        // control flow
        CASEB(expect)
        CASEB(unreachable)
        CASEB(trap)
        // bitwise operations
        CASEB(bswap16)
        CASEB(bswap32)
        CASEB(bswap64)
        CASEB(ffs)
        CASEB(ffsl)
        CASEB(ffsll)
        CASEB(clz)
        CASEB(clzl)
        CASEB(clzll)
        CASEB(ctz)
        CASEB(ctzl)
        CASEB(ctzll)
        CASEB(popcount)
        CASEB(popcountl)
        // memory operations
        CASEB(memset)
        CASEB(memcmp)
        CASEB(bzero)
#undef CASEB
    default:
        print.output() << "(Bin_unknown ";
        print.str(decl->getNameAsString());
        print.output() << ")";
        break;
    }
}

static inline Builtin::ID
builtin_id(const Decl *d) {
    if (const FunctionDecl *fd = dyn_cast_or_null<const FunctionDecl>(d)) {
        if (Builtin::ID::NotBuiltin != fd->getBuiltinID()) {
            return Builtin::ID(fd->getBuiltinID());
        }
    }
    return Builtin::ID::NotBuiltin;
}

void
parameter(const ParmVarDecl *decl, CoqPrinter &print, ClangPrinter &cprint) {
    print.output() << fmt::lparen;
    cprint.printParamName(decl, print);
    print.output() << "," << fmt::nbsp;
    cprint.printQualType(decl->getType(), print);
    print.output() << fmt::rparen;
}

void
printFunction(const FunctionDecl *decl, CoqPrinter &print,
              ClangPrinter &cprint) {
    print.ctor("Build_Func");
    cprint.printQualType(decl->getReturnType(), print);
    print.output() << fmt::nbsp << fmt::line;

    print.list(decl->parameters(), [&cprint](auto print, auto *i) {
        parameter(i, print, cprint);
    }) << fmt::nbsp;

    cprint.printCallingConv(getCallingConv(decl), print);
    print.output() << fmt::nbsp;

    if (decl->getBody()) {
        print.ctor("Some", false);
        print.ctor("Impl", false);
        cprint.printStmt(decl->getBody(), print);
        print.end_ctor();
        print.end_ctor();
    } else if (auto builtin = builtin_id(decl)) {
        print.ctor("Some", false);
        print.ctor("Builtin", false);
        PrintBuiltin(builtin, decl, print, cprint);
        print.end_ctor();
        print.end_ctor();
    } else {
        print.output() << "None";
    }
    print.end_ctor();
}

void
printMethod(const CXXMethodDecl *decl, CoqPrinter &print,
            ClangPrinter &cprint) {
    print.ctor("Build_Method");
    cprint.printQualType(decl->getCallResultType(), print);
    print.output() << fmt::line;
    cprint.printGlobalName(decl->getParent(), print);
    print.output() << fmt::line;
    cprint.printQualifier(decl->isConst(), decl->isVolatile(), print);
    print.output() << fmt::nbsp;

    print.list(decl->parameters(), [&cprint](auto print, auto i) {
        parameter(i, print, cprint);
    }) << fmt::nbsp;

    cprint.printCallingConv(getCallingConv(decl), print);
    print.output() << fmt::nbsp;

    print.output() << fmt::line;
    if (decl->getBody()) {
        print.ctor("Some", false);
        cprint.printStmt(decl->getBody(), print);
        print.end_ctor();
    } else {
        print.output() << "None";
    }

    print.end_ctor();
}

void
printDestructor(const CXXDestructorDecl *decl, CoqPrinter &print,
                ClangPrinter &cprint) {
    auto record = decl->getParent();
    print.ctor("Build_Dtor");
    cprint.printGlobalName(record, print);
    print.output() << fmt::nbsp;

    cprint.printCallingConv(getCallingConv(decl), print);
    print.output() << fmt::line;

    if (decl->isDefaulted()) {
        // todo(gmm): I need to generate this.
        print.output() << "(Some Defaulted)";
    } else if (decl->getBody()) {
        print.some();
        print.ctor("UserDefined");
        print.begin_tuple();
        cprint.printStmt(decl->getBody(), print);
        print.next_tuple();

        print.begin_list();
        // i need to destruct each field, and then each parent class
        // in the REVERSE order of construction
        {
            std::list<const FieldDecl *> fields(record->field_begin(),
                                                record->field_end());
            for (auto i = fields.crbegin(), e = fields.crend(); i != e; i++) {
                const FieldDecl *fd = *i;
                if (auto rd =
                        fd->getType().getTypePtr()->getAsCXXRecordDecl()) {
                    print.begin_tuple();
                    print.output()
                        << "Field \"" << fd->getName() << "\"," << fmt::nbsp;
                    cprint.printGlobalName(rd->getDestructor(), print);
                    print.end_tuple();
                    print.cons();
                }
            }
        }

        // base classes
        {
            std::list<CXXBaseSpecifier> bases(record->bases_begin(),
                                              record->bases_end());
            for (auto i = bases.crbegin(), e = bases.crend(); i != e; i++) {
                if (i->isVirtual()) {
                    using namespace logging;
                    fatal() << "virtual base classes are not supported.";
                }
                auto rec = i->getType().getTypePtr()->getAsCXXRecordDecl();
                if (rec) {
                    print.ctor("Base");
                    cprint.printGlobalName(rec, print);
                    print.output() << "," << fmt::nbsp;
                    cprint.printGlobalName(rec->getDestructor(), print);
                    print.output() << fmt::rparen;
                } else {
                    using namespace logging;
                    fatal() << "base class is not a RecordType.";
                    assert(false);
                }
                print.output() << "::";
            }
        }
        print.end_list();
        print.end_tuple();
        print.end_ctor();
        print.end_ctor();
    } else {
        print.none();
    }

    print.end_ctor();
}

class PrintDecl :
    public ConstDeclVisitorArgs<PrintDecl, bool, CoqPrinter &, ClangPrinter &,
                                const ASTContext &> {
private:
    PrintDecl() {}

public:
    static PrintDecl printer;

    bool VisitDecl(const Decl *d, CoqPrinter &print, ClangPrinter &cprint,
                   const ASTContext &) {
        using namespace logging;
        fatal() << "visiting declaration..." << d->getDeclKindName() << "(at "
                << cprint.sourceRange(d->getSourceRange()) << ")\n";
        die();
        return false;
    }

    bool VisitTypeDecl(const TypeDecl *type, CoqPrinter &print,
                       ClangPrinter &cprint, const ASTContext &) {
        using namespace logging;
        fatal() << "unsupported type declaration `" << type->getDeclKindName()
                << "(at " << cprint.sourceRange(type->getSourceRange())
                << ")\n";
        die();
        return false;
    }

    bool VisitEmptyDecl(const EmptyDecl *decl, CoqPrinter &print,
                        ClangPrinter &cprint, const ASTContext &) {
        // ignore
        return false;
    }

    bool VisitTypedefNameDecl(const TypedefNameDecl *type, CoqPrinter &print,
                              ClangPrinter &cprint, const ASTContext &) {
        print.ctor("Dtypedef")
            << "\"" << type->getNameAsString() << "\"" << fmt::nbsp;
        cprint.printQualType(type->getUnderlyingType(), print);
        print.end_ctor();
        return true;
    }

    bool printMangledFieldName(const FieldDecl *field, CoqPrinter &print,
                               ClangPrinter &cprint) {
        if (field->isAnonymousStructOrUnion()) {
            print.ctor("Nanon", false);
            cprint.printGlobalName(field->getType()->getAsCXXRecordDecl(),
                                   print);
            print.end_ctor();
        } else {
            print.str(field->getName());
        }
        return true;
    }

    void printFieldInitializer(const FieldDecl *field, CoqPrinter &print,
                               ClangPrinter &cprint) {
        Expr *expr = field->getInClassInitializer();
        if (expr != nullptr) {
            print.ctor("Some");
            cprint.printExpr(expr, print);
            print.end_ctor();
        } else {
            print.none();
        }
    }

    bool printFields(const CXXRecordDecl *decl, const ASTRecordLayout &layout,
                     CoqPrinter &print, ClangPrinter &cprint) {
        auto i = 0;
        print.begin_list();
        for (const FieldDecl *field : decl->fields()) {
            if (field->isBitField()) {
                logging::fatal()
                    << "bit fields are not supported "
                    << cprint.sourceRange(field->getSourceRange()) << "\n";
                logging::die();
            }
            print.output() << "(";
            printMangledFieldName(field, print, cprint);
            print.output() << "," << fmt::nbsp;
            cprint.printQualType(field->getType(), print);
            print.output() << "," << fmt::nbsp;
            printFieldInitializer(field, print, cprint);
            print.output() << "," << fmt::nbsp;
            print.output() << "Build_LayoutInfo " << layout.getFieldOffset(i++)
                           << ")";
            print.cons();
        };
        print.end_list();
        return true;
    }

    bool VisitUnionDecl(const CXXRecordDecl *decl, CoqPrinter &print,
                        ClangPrinter &cprint, const ASTContext &ctxt) {
        assert(decl->getTagKind() == TagTypeKind::TTK_Union);

        const auto &layout = ctxt.getASTRecordLayout(decl);
        print.ctor("Dunion");

        cprint.printGlobalName(decl, print);
        print.output() << fmt::nbsp;
        if (!decl->isCompleteDefinition()) {
            print.none();
            print.end_ctor();
            return true;
        }

        print.some();

        print.ctor("Build_Union");
        printFields(decl, layout, print, cprint);

        print.output() << fmt::line << layout.getSize().getQuantity()
                       << fmt::nbsp;

        print.end_ctor();
        print.end_ctor();
        print.end_ctor();
        return true;
    }

    bool VisitStructDecl(const CXXRecordDecl *decl, CoqPrinter &print,
                         ClangPrinter &cprint, const ASTContext &ctxt) {
        assert(decl->getTagKind() == TagTypeKind::TTK_Class ||
               decl->getTagKind() == TagTypeKind::TTK_Struct);
        auto &layout = ctxt.getASTRecordLayout(decl);
        print.ctor("Dstruct");
        cprint.printGlobalName(decl, print);
        print.output() << fmt::nbsp;
        if (!decl->isCompleteDefinition()) {
            print.none();
            print.end_ctor();
            return true;
        }

        print.some();
        print.ctor("Build_Struct");

        // print the base classes
        print.begin_list();
        for (auto base : decl->bases()) {
            if (base.isVirtual()) {
                logging::unsupported()
                    << "virtual base classes not supported\n";
            }

            auto rec = base.getType().getTypePtr()->getAsCXXRecordDecl();
            if (rec) {
                print.output() << "(";
                cprint.printGlobalName(rec, print);
                print.output()
                    << ", Build_LayoutInfo "
                    << layout.getBaseClassOffset(rec).getQuantity() << ")";
            } else {
                using namespace logging;
                fatal() << "base class is not a RecordType at "
                        << cprint.sourceRange(decl->getSourceRange()) << "\n";
                die();
            }
            print.cons();
        }
        print.end_list();

        // print the fields
        print.output() << fmt::line;
        printFields(decl, layout, print, cprint);

        // print the layout information
        print.output() << fmt::line;
        if (decl->isPOD()) {
            print.output() << "POD";
        } else if (decl->isStandardLayout()) {
            print.output() << "Standard";
        } else {
            print.output() << "Unspecified";
        }

        print.output() << fmt::nbsp << layout.getSize().getQuantity();

        // print the virtual function table
        print.begin_list();
        for (auto m : decl->methods()) {
            if (m->isVirtual()) {
                print.output() << "(";
                cprint.printGlobalName(m, print);
                print.output() << "," << fmt::nbsp;
                if (m->isPure()) {
                    print.none();
                } else {
                    print.some();
                    cprint.printGlobalName(m, print);
                    print.end_ctor();
                }
                print.output() << ")";
                print.cons();
            }
        }
        print.end_list();

        // print the virtual function table
        print.begin_list();
        for (auto m : decl->methods()) {
            if (m->isVirtual() and not m->isPure()) {
                for (auto o : m->overridden_methods()) {
                    print.output() << "(";
                    cprint.printGlobalName(o, print);
                    print.output() << "," << fmt::nbsp;
                    cprint.printGlobalName(m, print);
                    print.output() << ")";
                    print.cons();
                }
            }
        }
        print.end_list();

        if (decl->getDestructor() && decl->getDestructor()->isVirtual()) {
            print.some();
            cprint.printGlobalName(decl->getDestructor(), print);
            print.end_ctor();
        } else {
            print.none();
        }

        // todo(gmm): i need to print any implicit declarations.

        print.end_ctor();
        print.end_ctor();
        print.end_ctor();
        return true;
    }

    bool VisitCXXRecordDecl(const CXXRecordDecl *decl, CoqPrinter &print,
                            ClangPrinter &cprint, const ASTContext &ctxt) {
        if (!decl->isCompleteDefinition()) {
            print.ctor("Dtype");
            cprint.printGlobalName(decl, print);
            print.end_ctor();
        } else {
            switch (decl->getTagKind()) {
            case TagTypeKind::TTK_Class:
            case TagTypeKind::TTK_Struct:
                return VisitStructDecl(decl, print, cprint, ctxt);
            case TagTypeKind::TTK_Union:
                return VisitUnionDecl(decl, print, cprint, ctxt);
            case TagTypeKind::TTK_Interface:
            default:
                assert(false && "unknown record tag kind");
            }
        }
        return true;
    }

    bool VisitIndirectFieldDecl(const IndirectFieldDecl *decl,
                                CoqPrinter &print, ClangPrinter &cprint,
                                const ASTContext &) {
        return false;
    }

    bool VisitFunctionDecl(const FunctionDecl *decl, CoqPrinter &print,
                           ClangPrinter &cprint, const ASTContext &) {
        print.ctor("Dfunction");
        cprint.printGlobalName(decl, print);
        printFunction(decl, print, cprint);
        print.end_ctor();
        return true;
    }

    bool VisitCXXMethodDecl(const CXXMethodDecl *decl, CoqPrinter &print,
                            ClangPrinter &cprint, const ASTContext &) {
        if (decl->isStatic()) {
            print.ctor("Dfunction");
            cprint.printGlobalName(decl, print);
            printFunction(decl, print, cprint);
            print.end_ctor();
        } else {
            print.ctor("Dmethod");
            cprint.printGlobalName(decl, print);
            printMethod(decl, print, cprint);
            print.end_ctor();
        }
        return true;
    }

    bool VisitEnumConstantDecl(const EnumConstantDecl *decl, CoqPrinter &print,
                               ClangPrinter &cprint, const ASTContext &) {
        print.ctor("Dconstant");
        assert((decl != nullptr) && (!decl->getNameAsString().empty()));
        cprint.printGlobalName(decl, print);
        print.output() << fmt::nbsp;
        cprint.printQualType(decl->getType(), print);
        print.output() << fmt::nbsp;
        if (decl->getInitExpr()) {
            cprint.printExpr(decl->getInitExpr(), print);
        } else {
            print.ctor("Eint") << decl->getInitVal() << fmt::nbsp;
            cprint.printQualType(decl->getType(), print);
            print.output() << fmt::rparen;
        }
        print.end_ctor();
        return true;
    }

    bool VisitCXXConstructorDecl(const CXXConstructorDecl *decl,
                                 CoqPrinter &print, ClangPrinter &cprint,
                                 const ASTContext &) {
        print.ctor("Dconstructor");
        cprint.printGlobalName(decl, print);
        print.ctor("Build_Ctor");
        cprint.printGlobalName(decl->getParent(), print);
        print.output() << fmt::line;

        print.list(decl->parameters(), [&cprint](auto print, auto i) {
            parameter(i, print, cprint);
        });
        print.output() << fmt::nbsp;

        cprint.printCallingConv(getCallingConv(decl), print);

        if (decl->getBody()) {
            print.some();
            print.ctor("UserDefined");
            print.begin_tuple();

            // print the initializer list
            // note that implicit initialization is represented explicitly in this list
            // also, the order is corrrect with respect to initalization order
            print.begin_list();
            for (auto init : decl->inits()) {
                print.ctor("Build_Initializer");
                if (init->isMemberInitializer()) {
                    print.ctor("Field")
                        << "\"" << init->getMember()->getNameAsString() << "\"";
                    print.end_ctor();
                } else if (init->isBaseInitializer()) {
                    print.ctor("Base");
                    cprint.printGlobalName(
                        init->getBaseClass()->getAsCXXRecordDecl(), print);
                    print.end_ctor();
                } else if (init->isIndirectMemberInitializer()) {
                    auto im = init->getIndirectMember();
                    print.ctor("Indirect");

                    bool completed = false;
                    print.begin_list();
                    for (auto i : im->chain()) {
                        if (i->getName() == "") {
                            if (const FieldDecl *field =
                                    dyn_cast<FieldDecl>(i)) {
                                print.begin_tuple();
                                printMangledFieldName(field, print, cprint);
                                print.next_tuple();
                                cprint.printGlobalName(
                                    field->getType()->getAsCXXRecordDecl(),
                                    print);
                                print.end_tuple();
                                print.cons();
                            } else {
                                assert(false && "indirect field decl contains "
                                                "non FieldDecl");
                            }
                        } else {
                            completed = true;
                            print.end_list();
                            print.output() << fmt::nbsp;
                            print.str(i->getName());
                            break;
                        }
                    }
                    assert(completed && "didn't find a named field");

                    print.end_ctor();
                } else if (init->isDelegatingInitializer()) {
                    print.output() << "This";
                } else {
                    assert(false && "unknown initializer type");
                }
                print.output() << fmt::line;
                if (init->getMember()) {
                    cprint.printQualType(init->getMember()->getType(), print);
                } else if (init->getIndirectMember()) {
                    cprint.printQualType(init->getIndirectMember()->getType(),
                                         print);
                } else if (init->getBaseClass()) {
                    cprint.printType(init->getBaseClass(), print);
                } else if (init->isDelegatingInitializer()) {
                    cprint.printQualType(decl->getThisType(), print);
                } else {
                    assert(false && "not member, base class, or indirect");
                }
                print.output() << fmt::line;
                cprint.printExpr(init->getInit(), print);
                print.end_ctor();
                print.cons();
            }
            print.end_list();
            print.next_tuple();
            cprint.printStmt(decl->getBody(), print);
            print.end_tuple();
            print.end_ctor();
            print.end_ctor();
        } else {
            print.output() << fmt::nbsp;
            print.none();
        }
        print.end_ctor();
        print.end_ctor();
        return true;
    }

    bool VisitCXXDestructorDecl(const CXXDestructorDecl *decl,
                                CoqPrinter &print, ClangPrinter &cprint,
                                const ASTContext &ctxt) {
        print.ctor("Ddestructor");
        cprint.printGlobalName(decl, print);
        printDestructor(decl, print, cprint);
        print.end_ctor();
        return true;
    }

    bool VisitVarDecl(const VarDecl *decl, CoqPrinter &print,
                      ClangPrinter &cprint, const ASTContext &) {
        if (decl->isConstexpr()) {
            if (decl->hasInit()) {
                print.ctor("Dconstant");
                cprint.printGlobalName(decl, print);
                print.output() << fmt::nbsp;
                cprint.printQualType(decl->getType(), print);
                print.output() << fmt::nbsp;
                cprint.printExpr(decl->getInit(), print);
            } else { //no initializer
                print.ctor("Dconstant_undef");
                cprint.printGlobalName(decl, print);
                print.output() << fmt::nbsp;
                cprint.printQualType(decl->getType(), print);
            }
            print.end_ctor();
        } else if (decl->isTemplated()) {
            return false;
        } else {
            print.ctor("Dvar");

            cprint.printGlobalName(decl, print);
            print.output() << fmt::nbsp;
            cprint.printQualType(decl->getType(), print);
            print.output() << fmt::nbsp;
            if (decl->hasInit()) {
                print.some();
                cprint.printExpr(decl->getInit(), print);
                print.output() << fmt::rparen;
            } else {
                print.none();
            }
            print.end_ctor();
        }
        return true;
    }

    bool VisitUsingDecl(const UsingDecl *decl, CoqPrinter &print,
                        ClangPrinter &cprint, const ASTContext &) {
        return false;
    }

    bool VisitUsingDirectiveDecl(const UsingDirectiveDecl *decl,
                                 CoqPrinter &print, ClangPrinter &cprint,
                                 const ASTContext &) {
        return false;
    }

    bool VisitNamespaceDecl(const NamespaceDecl *decl, CoqPrinter &print,
                            ClangPrinter &cprint, const ASTContext &) {
        print.ctor(
            "Dnamespace") /* << "\"" << decl->getNameAsString() << "\"" */
            << fmt::line;
        print.begin_list();
        for (auto d : decl->decls()) {
            cprint.printDecl(d, print);
            print.cons();
        }
        print.end_list();
        print.end_ctor();
        return false;
    }

    bool VisitEnumDecl(const EnumDecl *decl, CoqPrinter &print,
                       ClangPrinter &cprint, const ASTContext &) {
        print.ctor("Denum");
        cprint.printGlobalName(decl, print);
        print.output() << fmt::nbsp;
        auto t = decl->getIntegerType();
        if (!t.isNull()) {
            print.ctor("Some", false);
            cprint.printQualType(decl->getIntegerType(), print);
            print.output() << fmt::rparen;
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;

        print.begin_list();
        for (auto i : decl->enumerators()) {
            print.output() << fmt::line << "(\"" << i->getNameAsString()
                           << "\"," << fmt::nbsp << "("
                           << i->getInitVal().getExtValue() << ")%Z)";
            print.cons();
        }
        print.end_list();

        print.end_ctor();
        return false;
    }

    bool VisitLinkageSpecDecl(const LinkageSpecDecl *decl, CoqPrinter &print,
                              ClangPrinter &cprint, const ASTContext &) {
        // we never print these things.
        assert(false);
        return false;
    }

    bool VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl,
                                   CoqPrinter &print, ClangPrinter &cprint,
                                   const ASTContext &) {
        // we only print specializations
        assert(false);
        return false;
    }

    bool VisitClassTemplateDecl(const ClassTemplateDecl *decl,
                                CoqPrinter &print, ClangPrinter &cprint,
                                const ASTContext &) {
        // we only print specializations
        assert(false);
        return false;
    }

    bool VisitFriendDecl(const FriendDecl *, CoqPrinter &, ClangPrinter &,
                         const ASTContext &) {
        return false;
    }

    bool VisitUsingShadowDecl(const UsingShadowDecl *, CoqPrinter &,
                              ClangPrinter &, const ASTContext &) {
        return false;
    }
};

PrintDecl PrintDecl::printer;

bool
ClangPrinter::printDecl(const clang::Decl *decl, CoqPrinter &print) {
    return PrintDecl::printer.Visit(decl, print, *this, *context_);
}
