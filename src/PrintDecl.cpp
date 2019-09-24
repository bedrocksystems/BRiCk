/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/RecordLayout.h"

using namespace clang;

void
printFunction(const FunctionDecl *decl, CoqPrinter &print,
              ClangPrinter &cprint) {
    print.output() << "{| f_return :=" << fmt::indent;
    cprint.printQualType(decl->getReturnType(), print);
    print.output() << fmt::line << "; f_params :=" << fmt::nbsp;

    for (auto i : decl->parameters()) {
        cprint.printParam(i, print);
        print.cons();
    }
    print.output() << "nil";

    print.output() << fmt::line << "; f_body :=" << fmt::nbsp;
    if (decl->getBody()) {
        print.ctor("Some", false);
        cprint.printStmt(decl->getBody(), print);
        print.output() << fmt::rparen;
    } else {
        print.output() << "None";
    }
    print.output() << fmt::outdent << "|}";
}

void
printMethod(const CXXMethodDecl *decl, CoqPrinter &print,
            ClangPrinter &cprint) {
    print.output() << "{| m_return :=" << fmt::indent;
    cprint.printQualType(decl->getCallResultType(), print);
    print.output() << fmt::line << "; m_class :=" << fmt::nbsp;
    cprint.printGlobalName(decl->getParent(), print);
    print.output() << fmt::line << "; m_this_qual :=" << fmt::indent;
    cprint.printQualifier(decl->isConst(), decl->isVolatile(), print);
    print.output() << "; m_params :=" << fmt::nbsp;

    for (auto i : decl->parameters()) {
        cprint.printParam(i, print);
        print.output() << "::";
    }
    print.output() << "nil";

    print.output() << fmt::line << "; m_body :=" << fmt::nbsp;
    if (decl->getBody()) {
        print.output() << fmt::lparen << "Some" << fmt::nbsp;
        cprint.printStmt(decl->getBody(), print);
        print.output() << fmt::rparen;
    } else {
        print.output() << "None";
    }

    print.output() << fmt::line << "; m_virtual := " << fmt::nbsp;
    if (decl->isVirtual()) {
        using namespace logging;
        unsupported() << "[ERR] virtual functions not supported: "
                      << decl->getNameAsString() << "\n";
    }
    print.boolean(decl->isVirtual());

    print.output() << fmt::outdent << "|}";
}

void
printConstructor(const CXXConstructorDecl *decl, CoqPrinter &print,
                 ClangPrinter &cprint) {
    // ignore
}

void
printDestructor(const CXXDestructorDecl *decl, CoqPrinter &print,
                ClangPrinter &cprint) {
    auto record = decl->getParent();
    print.output() << "{| d_class :=" << fmt::nbsp;
    cprint.printGlobalName(record, print);
    print.output() << fmt::line << " ; d_virtual := ";
    print.boolean(decl->isVirtual());
    print.output() << fmt::line << " ; d_body :=";

    if (decl->isDefaulted()) {
        // todo(gmm): I need to generate this.
        print.output() << "Some Defaulted |}";
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
                    // fatal("virtual base classes are not supported.");
                    assert(false);
                }
                auto rec = i->getType().getTypePtr()->getAsCXXRecordDecl();
                if (rec) {
                    print.ctor("Base");
                    cprint.printGlobalName(rec, print);
                    print.output() << "," << fmt::nbsp;
                    cprint.printGlobalName(rec->getDestructor(), print);
                    print.output() << fmt::rparen;
                } else {
                    //fatal("base class is not a RecordType.");
                    assert(false);
                }
                print.output() << "::";
            }
        }
        print.end_list();
        print.end_tuple();
        print.end_ctor();
        print.end_ctor();
        print.end_record();
    } else {
        print.none();
    }
}

class PrintDecl :
    public ConstDeclVisitorArgs<PrintDecl, void, CoqPrinter &, ClangPrinter &,
                                const ASTContext &> {
private:
    PrintDecl() {}

public:
    static PrintDecl printer;

    void VisitDecl(const Decl *d, CoqPrinter &print, ClangPrinter &cprint,
                   const ASTContext &) {
        using namespace logging;
        fatal() << "visiting declaration..." << d->getDeclKindName() << "(at "
                << cprint.sourceRange(d->getSourceRange()) << ")\n";
        die();
    }

    void VisitTypeDecl(const TypeDecl *type, CoqPrinter &print,
                       ClangPrinter &cprint, const ASTContext &) {
        using namespace logging;
        fatal() << "unsupported type declaration `" << type->getDeclKindName()
                << "(at " << cprint.sourceRange(type->getSourceRange())
                << ")\n";
        die();
    }

    void VisitEmptyDecl(const EmptyDecl *decl, CoqPrinter &print,
                        ClangPrinter &cprint, const ASTContext &) {
        // ignore
    }

    void VisitTypedefNameDecl(const TypedefNameDecl *type, CoqPrinter &print,
                              ClangPrinter &cprint, const ASTContext &) {
        print.ctor("Dtypedef")
            << "\"" << type->getNameAsString() << "\"" << fmt::nbsp;
        cprint.printQualType(type->getUnderlyingType(), print);
        print.output() << fmt::rparen;
    }

    void printMangledFieldName(const FieldDecl *field, CoqPrinter &print,
                               ClangPrinter &cprint) {
        if (field->isAnonymousStructOrUnion()) {
            print.ctor("Nanon", false);
            cprint.printGlobalName(field->getType()->getAsCXXRecordDecl(),
                                   print);
            print.end_ctor();
        } else {
            print.str(field->getName());
        }
    }

    void printFields(const CXXRecordDecl *decl, const ASTRecordLayout &layout,
                     CoqPrinter &print, ClangPrinter &cprint) {
        auto i = 0;
        for (const FieldDecl *field : decl->fields()) {
            print.output() << "(";
            printMangledFieldName(field, print, cprint);
            print.output() << "," << fmt::nbsp;
            cprint.printQualType(field->getType(), print);
            print.output() << "," << fmt::nbsp;
            print.output() << "{| li_offset := " << layout.getFieldOffset(i++)
                           << fmt::nbsp << "|})";
            print.cons();
        };
        print.output() << "nil";
    }

    void VisitUnionDecl(const CXXRecordDecl *decl, CoqPrinter &print,
                        ClangPrinter &cprint, const ASTContext &ctxt) {
        assert(decl->getTagKind() == TagTypeKind::TTK_Union);

        const auto &layout = ctxt.getASTRecordLayout(decl);
        print.ctor("Dunion");

        cprint.printGlobalName(decl, print);
        print.output() << fmt::nbsp;
        if (!decl->isCompleteDefinition()) {
            print.output() << "None" << fmt::rparen;
            return;
        }

        print.ctor("Some", false);

        print.begin_record();
        print.record_field("u_fields");
        printFields(decl, layout, print, cprint);

        print.output() << fmt::line
                       << " ; u_size := " << layout.getSize().getQuantity()
                       << fmt::nbsp;

        print.end_record();
        print.output() << fmt::rparen << fmt::rparen;
    }

    void VisitStructDecl(const CXXRecordDecl *decl, CoqPrinter &print,
                         ClangPrinter &cprint, const ASTContext &ctxt) {
        assert(decl->getTagKind() == TagTypeKind::TTK_Class ||
               decl->getTagKind() == TagTypeKind::TTK_Struct);
        auto &layout = ctxt.getASTRecordLayout(decl);
        print.ctor("Dstruct");
        cprint.printGlobalName(decl, print);
        print.output() << fmt::nbsp;
        if (!decl->isCompleteDefinition()) {
            print.output() << "None" << fmt::rparen;
            return;
        }

        print.ctor("Some", false);

        // print the base classes
        print.output() << fmt::line << "{| s_bases :=" << fmt::nbsp;
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
                    << ", {| li_offset :="
                    << layout.getBaseClassOffset(rec).getQuantity() << "|})";
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
        print.output() << fmt::line << " ; s_fields :=" << fmt::indent
                       << fmt::line;
        printFields(decl, layout, print, cprint);
        print.output() << fmt::outdent << fmt::line;

        // print the layout information
        print.output() << fmt::line << " ; s_layout :=" << fmt::nbsp;
        if (decl->isPOD()) {
            print.output() << "POD";
        } else if (decl->isStandardLayout()) {
            print.output() << "Standard";
        } else {
            print.output() << "Unspecified";
        }

        print.output() << fmt::line
                       << " ; s_size := " << layout.getSize().getQuantity();

        // todo(gmm): i need to print any implicit declarations.

        print.output() << "|}" << fmt::rparen << fmt::rparen;
    }

    void VisitCXXRecordDecl(const CXXRecordDecl *decl, CoqPrinter &print,
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
    }

    void VisitIndirectFieldDecl(const IndirectFieldDecl *decl,
                                CoqPrinter &print, ClangPrinter &cprint,
                                const ASTContext &) {
        assert(true);
    }

    void VisitFunctionDecl(const FunctionDecl *decl, CoqPrinter &print,
                           ClangPrinter &cprint, const ASTContext &) {
        print.ctor("Dfunction");
        cprint.printGlobalName(decl, print);
        print.output() << fmt::line;
        printFunction(decl, print, cprint);
        print.end_ctor();
    }

    void VisitCXXMethodDecl(const CXXMethodDecl *decl, CoqPrinter &print,
                            ClangPrinter &cprint, const ASTContext &) {
        if (decl->isStatic()) {
            print.ctor("Dfunction");
            cprint.printGlobalName(decl, print);
            print.output() << fmt::line << fmt::indent;
            printFunction(decl, print, cprint);
            print.output() << fmt::outdent;
            print.end_ctor();
        } else {
            print.ctor("Dmethod");
            cprint.printGlobalName(decl, print);
            print.output() << fmt::line << fmt::indent;
            printMethod(decl, print, cprint);
            print.output() << fmt::outdent;
            print.end_ctor();
        }
    }

    void VisitEnumConstantDecl(const EnumConstantDecl *decl, CoqPrinter &print,
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
        print.output() << fmt::rparen;
    }

    void VisitCXXConstructorDecl(const CXXConstructorDecl *decl,
                                 CoqPrinter &print, ClangPrinter &cprint,
                                 const ASTContext &) {
        print.ctor("Dconstructor");
        cprint.printGlobalName(decl, print);
        print.output() << fmt::line;
        print.output() << "{| c_class :=" << fmt::nbsp;
        cprint.printGlobalName(decl->getParent(), print);
        print.output() << fmt::line << " ; c_params :=" << fmt::nbsp;

        for (auto i : decl->parameters()) {
            cprint.printParam(i, print);
            print.output() << "::";
        }
        print.output() << "nil";

        print.output() << fmt::line << " ; c_body :=" << fmt::nbsp;
        if (decl->getBody()) {
            print.output() << "Some" << fmt::nbsp;
            print.ctor("UserDefined");
            print.begin_tuple();

            // print the initializer list
            // todo(gmm): parent constructors are defaulted if they are not listed,
            //   i need to make sure that everything ends up in the list, and in the right order
            print.begin_list();
            for (auto init : decl->inits()) {
                print.begin_record();
                print.record_field("init_path");
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
                } else {
                    assert(false && "unknown initializer type");
                }
                print.output() << ";" << fmt::nbsp;
                print.record_field("init_type");
                if (init->getMember()) {
                    cprint.printQualType(init->getMember()->getType(), print);
                } else if (init->getIndirectMember()) {
                    cprint.printQualType(init->getIndirectMember()->getType(),
                                         print);
                } else if (init->getBaseClass()) {
                    cprint.printType(init->getBaseClass(), print);
                } else {
                    assert(false && "not member, base class, or indirect");
                }
                print.output() << ";" << fmt::nbsp;
                print.record_field("init_init");
                cprint.printExpr(init->getInit(), print);
                print.end_record();
                print.cons();
            }
            print.end_list();
            print.next_tuple();
            cprint.printStmt(decl->getBody(), print);
            print.end_tuple();
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << "|}";
        print.output() << fmt::rparen;
    }

    void VisitCXXDestructorDecl(const CXXDestructorDecl *decl,
                                CoqPrinter &print, ClangPrinter &cprint,
                                const ASTContext &ctxt) {
        print.ctor("Ddestructor");
        cprint.printGlobalName(decl, print);
        print.output() << fmt::line;
        printDestructor(decl, print, cprint);
        print.output() << fmt::rparen;
    }

    void VisitVarDecl(const VarDecl *decl, CoqPrinter &print,
                      ClangPrinter &cprint, const ASTContext &) {
        if (decl->isConstexpr()) {
            print.ctor("Dconstant");
            cprint.printGlobalName(decl, print);
            print.output() << fmt::nbsp;
            cprint.printQualType(decl->getType(), print);
            print.output() << fmt::nbsp;
            if (decl->getInit() == nullptr) {
                using namespace logging;
                fatal() << "missing initailization of constexpr "
                        << cprint.sourceRange(decl->getSourceRange()) << "\n";
                die();
            }
            cprint.printExpr(decl->getInit(), print);
            print.output() << fmt::rparen;
        } else {
            print.ctor("Dvar");
            cprint.printGlobalName(decl, print);
            print.output() << fmt::nbsp;
            cprint.printQualType(decl->getType(), print);
            if (decl->hasInit()) {
                print.some();
                cprint.printExpr(decl->getInit(), print);
                print.output() << fmt::rparen;
            } else {
                print.none();
            }
            print.output() << fmt::rparen;
        }
    }

    void VisitUsingDecl(const UsingDecl *decl, CoqPrinter &print,
                        ClangPrinter &cprint, const ASTContext &) {}

    void VisitUsingDirectiveDecl(const UsingDirectiveDecl *decl,
                                 CoqPrinter &print, ClangPrinter &cprint,
                                 const ASTContext &) {}

    void VisitNamespaceDecl(const NamespaceDecl *decl, CoqPrinter &print,
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
    }

    void VisitEnumDecl(const EnumDecl *decl, CoqPrinter &print,
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
                           << "\"," << fmt::nbsp
                           << i->getInitVal().getExtValue() << "%Z)";
            print.cons();
        }
        print.end_list();

        print.end_ctor();
    }

    void VisitLinkageSpecDecl(const LinkageSpecDecl *decl, CoqPrinter &print,
                              ClangPrinter &cprint, const ASTContext &) {
        // we never print these things.
        assert(false);
    }

    void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl,
                                   CoqPrinter &print, ClangPrinter &cprint,
                                   const ASTContext &) {
        // we only print specializations
        assert(false);
    }

    void VisitClassTemplateDecl(const ClassTemplateDecl *decl,
                                CoqPrinter &print, ClangPrinter &cprint,
                                const ASTContext &) {
        // we only print specializations
        assert(false);
    }
};

PrintDecl PrintDecl::printer;

void
ClangPrinter::printDecl(const clang::Decl *decl, CoqPrinter &print) {
    PrintDecl::printer.Visit(decl, print, *this, *context_);
}
