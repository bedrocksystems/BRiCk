/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include "CoqPrinter.hpp"
#include "ClangPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "clang/AST/Decl.h"
#include <Formatter.hpp>

using namespace clang;

void printFunction(
        const FunctionDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
{
  print.output() << "{| f_return :=" << fmt::indent;
  cprint.printQualType(decl->getCallResultType(), print);
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

void printMethod(
        const CXXMethodDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
{
  print.output() << "{| m_return :=" << fmt::indent;
  cprint.printQualType(decl->getCallResultType(), print);
  print.output() << fmt::line << "; m_class :=" << fmt::nbsp;
  cprint.printGlobalName(decl->getParent(), print);
  print.output() << fmt::line << "; m_this_qual :=" << fmt::indent;
  print.output() << "{| q_const :=" << (decl->isConst() ? "true" : "false")
                 << "; q_volatile :=" << (decl->isVolatile() ? "true" : "false")
                 << "|}" << fmt::outdent << fmt::line;
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
  print.output() << fmt::outdent << "|}";
}

void printConstructor(
        const CXXConstructorDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
{

}

void printDestructor(
        const CXXDestructorDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
{
  auto record = decl->getParent();
  print.output() << "{| d_class :=" << fmt::nbsp;
  cprint.printGlobalName(record, print);
  print.output() << fmt::line << " ; d_body :=";
  if (decl->isDefaulted()) {
    // todo(gmm): I need to generate this.
    print.output() << "Some Defaulted |}";
  } else if (decl->getBody()) {
    print.output() << "Some" << fmt::nbsp;
    print.ctor("UserDefined") << fmt::lparen;
    cprint.printStmt(decl->getBody(), print);
    print.output() << "," << fmt::nbsp;

    // i need to destruct each field, and then each parent class
    // in the REVERSE order of construction
    {
      std::list<const FieldDecl *> fields(
              record->field_begin(), record->field_end());
      for (auto i = fields.crbegin(), e = fields.crend(); i != e; i++) {
        const FieldDecl *fd = *i;
        if (auto rd = fd->getType().getTypePtr()->getAsCXXRecordDecl()) {
          print.ctor("Field") << "\"" << fd->getName() << "\"";
          cprint.printGlobalName(rd->getDestructor(), print);
          print.output() << fmt::rparen << fmt::nbsp << "::";
        }
      }
    }

    // base classes
    {
      std::list<CXXBaseSpecifier> bases(
              record->bases_begin(), record->bases_end());
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
    print.output() << "nil";

    print.output() << fmt::rparen << fmt::rparen << "|}";
  } else {
    print.error() << "destructor has no body\n";
    print.output() << "None";
  }
}

class PrintDecl : public ConstDeclVisitorArgs<PrintDecl, void, CoqPrinter &,
                          ClangPrinter &> {
  private:
  PrintDecl() {}

  public:
  static PrintDecl printer;

  void VisitDecl(const Decl *d, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.error() << "visiting declaration..." << d->getDeclKindName() << "\n";
  }

  void VisitTypeDecl(
          const TypeDecl *type, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.error() << "unsupported type declaration `" << type->getDeclKindName()
            << "`\n";
  }

  void VisitEmptyDecl(
          const EmptyDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
  }

  void VisitTypedefNameDecl(
          const TypedefNameDecl *type, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Dtypedef")
            << "\"" << type->getNameAsString() << "\"" << fmt::nbsp;
    cprint.printQualType(type->getUnderlyingType(), print);
    print.output() << fmt::rparen;
  }

  void printMangledFieldName(const FieldDecl *field, CoqPrinter &print, ClangPrinter &cprint) {
    if (field->isAnonymousStructOrUnion()) {
      print.ctor("Nanon", false);
      cprint.printGlobalName(field->getType()->getAsCXXRecordDecl(), print);
      print.end_ctor();
    } else {
      print.str(field->getName());
    }
  }

  void printFields(const CXXRecordDecl *decl, CoqPrinter &print, ClangPrinter &cprint) {
    for (const FieldDecl *field : decl->fields()) {
      print.output() << "(";
      printMangledFieldName(field, print, cprint);
      print.output() << "," << fmt::nbsp;
      cprint.printQualType(field->getType(), print);
      print.output() << "," << fmt::nbsp;
      if (const Expr *init = field->getInClassInitializer()) {
        print.ctor("Some", false);
        cprint.printExpr(init, print);
        print.output() << fmt::rparen;
      } else {
        print.output() << "None";
      }
      print.output() << ")";
      print.cons();
    };
    print.output() << "nil";
  }

  void VisitUnionDecl(const CXXRecordDecl *decl, CoqPrinter &print, ClangPrinter &cprint) {
    assert(decl->getTagKind() == TagTypeKind::TTK_Union);
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
    printFields(decl, print, cprint);
    print.end_record();
    print.output() << fmt::rparen << fmt::rparen;
  }

  void VisitStructDecl(const CXXRecordDecl *decl, CoqPrinter &print, ClangPrinter &cprint) {
    assert(decl->getTagKind() == TagTypeKind::TTK_Class || decl->getTagKind() == TagTypeKind::TTK_Struct);

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
    for (auto base : decl->bases()) {
      if (base.isVirtual()) {
        print.error() << "virtual base classes not supported\n";
      }

      auto rec = base.getType().getTypePtr()->getAsCXXRecordDecl();
      if (rec) {
        cprint.printGlobalName(rec, print);
      } else {
        print.error() << "base class is not a RecordType";
      }
      print.output() << "::";
    }
    print.output() << "nil";

    // print the fields
    print.output() << fmt::line << " ; s_fields :=" << fmt::indent << fmt::line;
    printFields(decl, print, cprint);

    // todo(gmm): i need to print any implicit declarations.

    print.output() << fmt::outdent << fmt::line << "|}" << fmt::rparen << fmt::rparen;
  }

  void VisitCXXRecordDecl(const CXXRecordDecl *decl, CoqPrinter &print, ClangPrinter &cprint) {
    switch (decl->getTagKind()) {
      case TagTypeKind::TTK_Class:
      case TagTypeKind::TTK_Struct:
        return VisitStructDecl(decl, print, cprint);
      case TagTypeKind::TTK_Union:
        return VisitUnionDecl(decl, print, cprint);
      case TagTypeKind::TTK_Interface:
      default:
        assert(false && "unknown record tag kind");
    }
  }

  void VisitIndirectFieldDecl(const IndirectFieldDecl *decl, CoqPrinter &print, ClangPrinter &cprint) {
    assert(true);
  }

  void VisitFunctionDecl(const FunctionDecl *decl, CoqPrinter &print, ClangPrinter &cprint) {
    print.ctor("Dfunction");
    cprint.printGlobalName(decl, print);
    print.output() << fmt::line;
    printFunction(decl, print, cprint);
    print.output() << fmt::rparen;
  }

  void VisitCXXMethodDecl(
          const CXXMethodDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    if (decl->isStatic()) {
      print.ctor("Dfunction") << "\"" << decl->getNameAsString() << "\"" << fmt::line;
      printFunction(decl, print, cprint);
      print.output() << fmt::rparen;
    } else {
      if (decl->isVirtual()) {
        print.error() << "[ERR] virtual functions not supported: "
                << decl->getNameAsString() << "\n";
      } else {
        print.ctor("Dmethod");
        cprint.printGlobalName(decl, print);
        print.output() << fmt::line << fmt::indent;
        printMethod(decl, print, cprint);
        print.output() << fmt::outdent << fmt::rparen;
      }
    }
  }

  void VisitEnumConstantDecl(const EnumConstantDecl *decl,
          CoqPrinter &print, ClangPrinter &cprint) {
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
          CoqPrinter &print, ClangPrinter &cprint)
  {
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
        print.begin_tuple();
        if (init->isMemberInitializer()) {
          print.ctor("Field") << "\""
                        << init->getMember()->getNameAsString() << "\"";
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
              if (const FieldDecl *field = dyn_cast<FieldDecl>(i)) {
                print.begin_tuple();
                printMangledFieldName(field, print, cprint);
                print.next_tuple();
                cprint.printGlobalName(field->getType()->getAsCXXRecordDecl(), print);
                print.end_tuple();
                print.cons();
              } else {
                assert(false && "indirect field decl contains non FieldDecl");
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
        print.next_tuple();
        cprint.printExpr(init->getInit(), print);
        print.end_tuple();
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

  void VisitCXXDestructorDecl(const CXXDestructorDecl *decl, CoqPrinter &print,
          ClangPrinter &cprint)
  {
    print.ctor("Ddestructor");
    cprint.printGlobalName(decl, print);
    print.output() << fmt::line;
    printDestructor(decl, print, cprint);
    print.output() << fmt::rparen;
  }

  void VisitVarDecl(const VarDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    if (decl->isConstexpr()) {
      print.ctor("Dconstant");
      cprint.printGlobalName(decl, print);
      print.output() << fmt::nbsp;
      cprint.printQualType(decl->getType(), print);
      print.output() << fmt::nbsp;
      assert(decl->getInit() && "missing initialization of constexpr");
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

  void VisitUsingDecl(
          const UsingDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
  }

  void VisitUsingDirectiveDecl(const UsingDirectiveDecl *decl,
          CoqPrinter &print, ClangPrinter &cprint)
  {
  }

  void VisitNamespaceDecl(
          const NamespaceDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Dnamespace") /* << "\"" << decl->getNameAsString() << "\"" */
            << fmt::line;
    print.begin_list();
    for (auto d : decl->decls()) {
      cprint.printDecl(d, print);
      print.cons();
    }
    print.end_list();
    print.end_ctor();
  }

  void VisitEnumDecl(const EnumDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    if (decl->getName() == "") {
      assert(false && "anonymous enumerations are not supported");
    }
    print.ctor("Denum") << "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;
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
      print.output() << fmt::line << "(\"" << i->getNameAsString() << "\"," << fmt::nbsp << i->getInitVal().getExtValue() << "%Z)";
      print.cons();
    }
    print.end_list();

    print.end_ctor();
  }

  void VisitLinkageSpecDecl(
          const LinkageSpecDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    // we never print these things.
    assert(false);
  }

  void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl,
          CoqPrinter &print, ClangPrinter &cprint)
  {
    assert(false);
#if 0
    // note(gmm): for now, i am just going to return the specializations.
    for (auto i : decl->specializations()) {
      cprint.printDecl(i, print);
      print.output() << "::";
    }
#endif
  }

  void VisitClassTemplateDecl(const ClassTemplateDecl *decl, CoqPrinter &print,
          ClangPrinter &cprint)
  {
    assert(false);
#if 0
    for (auto i : decl->specializations()) {
      cprint.printDecl(i, print);
      print.output() << "::";
    }
#endif
  }
};

PrintDecl PrintDecl::printer;

void ClangPrinter::printDecl(const clang::Decl *decl, CoqPrinter &print)
{
  PrintDecl::printer.Visit(decl, print, *this);
}
