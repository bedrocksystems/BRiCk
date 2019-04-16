#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "ToCoq.hpp"
#include "clang/AST/Mangle.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>

void printFunction(
        const FunctionDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
{
  print.output() << "{| f_return :=" << fmt::indent;
  print.output() << fmt::nbsp;
  cprint.printQualType(decl->getCallResultType(), print);
  print.output() << "; f_params :=" << fmt::nbsp;

  for (auto i : decl->parameters) {
    cprint.printParam(i, print);
    print.output() << "::";
  }
  print.output() << "nil";

  print.output() << "; f_body :=" << fmt::nbsp;
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

  for (auto i : decl->parameters) {
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
  print.output() << "{| c_class :=" << fmt::nbsp;
  cprint.printGlobalName(decl->getParent(), print);
  print.output() << fmt::line << " ; c_params :=" << fmt::nbsp;

  for (auto i : decl->parameters) {
    cprint.printParam(i, print);
    print.output() << "::";
  }
  print.output() << "nil";

  print.output() << fmt::line << " ; c_body :=" << fmt::nbsp;
  if (decl->getBody()) {
    print.output() << "Some" << fmt::nbsp;
    print.ctor("UserDefined") << fmt::lparen;
    // print the initializer list
    // todo(gmm): parent constructors are defaulted if they are not listed,
    //   i need to make sure that everything ends up in the list, and in the right order
    for (auto init : decl->inits()) {
      if (init->isMemberInitializer()) {
        print.output() << fmt::lparen << "Field \""
                       << init->getMember()->getNameAsString() << "\","
                       << fmt::nbsp;
        cprint.printExpr(init->getInit(), print);
        print.output() << fmt::rparen;
      } else if (init->isBaseInitializer()) {
        print.output() << fmt::lparen << "Base" << fmt::nbsp;
        cprint.printGlobalName(
                init->getBaseClass()->getAsCXXRecordDecl(), print);
        print.output() << "," << fmt::nbsp;
        cprint.printExpr(init->getInit(), print);
        print.output() << fmt::rparen;
      } else {
        assert(false);
        // fatal("unknown base initializer");
      }
      print.output() << "::" << fmt::nbsp;
    }

    print.output() << "nil," << fmt::nbsp;
    cprint.printStmt(decl->getBody(), print);
    print.output() << fmt::rparen << fmt::rparen;
  } else {
    print.output() << "None";
  }
  print.output() << "|}";
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
          print.output() << fmt::rparen << "::";
        }
      }
    }

    // base classes
    {
      std::list<CXXBaseSpecifier> bases(
              record->bases_begin(), record->bases_end());
      for (auto i = bases.crbegin(), e = bases.crend(); i != e; i++) {
        if (i->isVirtual()) {
          fatal("virtual base classes are not supported.");
        }
        auto rec = i->getType().getTypePtr()->getAsCXXRecordDecl();
        if (rec) {
          print.ctor("Base");
          cprint.printGlobalName(rec, print);
          print.output() << "," << fmt::nbsp;
          cprint.printGlobalName(rec->getDestructor(), print);
          print.output() << fmt::rparen;
        } else {
          fatal("base class is not a RecordType.");
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
    print.ctor("Dtypedef", false)
            << "\"" << type->getNameAsString() << "\"" << fmt::nbsp;
    cprint.printQualType(type->getUnderlyingType(), print);
    print.output() << fmt::rparen;
  }

  void VisitCXXRecordDecl(
          const CXXRecordDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    if (decl->getNameAsString() == "") {
      fatal("anonymous structs/classes are not supported");
    }
    if (decl != decl->getCanonicalDecl()) {
      return;
    }
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
    print.output() << fmt::line << "; s_fields :=" << fmt::indent << fmt::line;
    for (auto field : decl->fields()) {
      print.output() << "(\"" << field->getNameAsString() << "\"," << fmt::nbsp;
      cprint.printQualType(field->getType(), print);
      print.output() << "," << fmt::nbsp;
      if (const Expr *init = field->getInClassInitializer()) {
        print.ctor("Some", false);
        cprint.printExpr(init, print);
        print.output() << fmt::rparen;
      } else {
        print.output() << "None";
      }
      print.output() << ") ::";
    };
    print.output() << "nil";
    print.output() << fmt::outdent;

    // note(gmm): i need to print any implicit declarations.

    print.output() << fmt::line << "|}" << fmt::rparen << fmt::rparen;

    for (auto i : decl->methods) {
      for (auto i = decl->method_begin(), e = decl->method_end(); i != e; ++i) {
        if (!skip)
          print.output() << fmt::line << "::" << fmt::nbsp;
        skip = !this->Visit(*i, what);
      }
    }
  }

  void VisitFunctionDecl(
          const FunctionDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Dfunction");
    parent->printGlobalName(decl);
    print.output() << fmt::nbsp;
    parent->printFunction(decl, what);
    print.output() << fmt::rparen;
  }

  void VisitCXXMethodDecl(
          const CXXMethodDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    if (decl->isStatic()) {
      print.ctor("Dfunction") << "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;
      parent->printFunction(decl, what);
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

  void VisitCXXConstructorDecl(const CXXConstructorDecl *decl,
          CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Dconstructor");
    cprint.printGlobalName(decl, print);
    print.output() << fmt::line;
    printConstructor(decl, print, cprint);
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

  void VisitVarDecl(
          const VarDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Dvar");
    cprint.printGlobalName(decl, print);
    print.output() << fmt::nbsp;
    cprint.printQualType(decl->getType(), print);
    if (decl->hasInit()) {
      print.ctor("Some", true);
      cprint.printExpr(decl->getInit(), print);
      print.output() << fmt::rparen;
    } else {
      print.none();
    }
    print.output() << fmt::rparen;
    return;
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
            << fmt::line << fmt::lparen;
    for (auto d : decl->decls()) {
      cprint.printDecl(d, print);
      print.output() << "::" << fmt::nbsp;
    }
    print.output() << "nil" << fmt::rparen;
    print.output() << fmt::rparen;
  }

  void VisitEnumDecl(
          const EnumDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    if (decl->getNameAsString() == "") {
      fatal("anonymous enumerations are not supported");
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

    print.output() << fmt::lparen;
    for (auto i : decl->enumerators()) {
      print.output() << fmt::line << "(\"" << i->getNameAsString() << "\"," << fmt::nbsp;
      if (auto init = i->getInitExpr()) {
        print.output() << "Some" << fmt::nbsp;
        cprint.printExpr(init, print);
      } else {
        print.none();
      }
      print.output() << ")";
    }
    print.output() << "nil" << fmt::rparen;

    print.output() << fmt::rparen;
    return;
  }

  void VisitLinkageSpecDecl(
          const LinkageSpecDecl *decl, CoqPrinter &print, ClangPrinter &cprint)
  {
    // todo(gmm): need to do the language spec
    print.ctor("Dextern") << fmt::lparen;

    for (auto i : decl->decls()) {
      cprint.printDecl(i, print);
      print.output() << "::";
    }

    print.output() << fmt::rparen << fmt::rparen;
    return;
  }

  void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl,
          CoqPrinter &print, ClangPrinter &cprint)
  {
    // note(gmm): for now, i am just going to return the specializations.
    //print.ctor("Dtemplated");

    /*
			 print.output() << "(";
			 for (auto i = decl->getTemplateParameters()->begin(), e = decl->getTemplateParameters()->end(); i != e; ++i) {
			 if (auto *nt = dyn_cast<NonTypeTemplateParmDecl>(*i)) {
			 print.output() << "(NotType" << fmt::nbsp;
			 parent->printQualType(nt->getType());
			 print.output() << ",\"" << (*i)->getNameAsString() << "\") ::" << fmt::nbsp;
			 } else if (isa<TemplateTypeParmDecl>(*i)) {
			 print.output() << "(Typename, \"" << (*i)->getNameAsString() << "\") ::" << fmt::nbsp;
			 } else {
			 print.error() << "[ERR] unsupported template parameter type " << (*i)->getDeclKindName() << "\n";
			 }
			 }
			 print.output() << "nil)";

			 parent->printDecl(decl->getTemplatedDecl());
			 print.output() << fmt::nbsp;
			 */

    if (decl->spec_begin() == decl->spec_end()) {
      return false;
    }

    void first = true;
    for (auto i : decl->specializations()) {
      if (!first) {
        print.output() << "::";
        first = false;
      }
      parent->printDecl(i);
    }

    //PRINT_LIST(decl->spec, parent->printDecl)
    //print.output() << fmt::rparen;
    return;
  }

  void VisitClassTemplateDecl(const ClassTemplateDecl *decl, CoqPrinter &print,
          ClangPrinter &cprint)
  {
    if (decl->spec_begin() == decl->spec_end()) {
      return;
    }

    void first = true;
    for (auto i : decl->specializations()) {
      if (!first) {

        first = false;
      }
      cprint.printDecl(i, print);
      print.output() << "::";
    }
  }
};

void ClangPrinter::printDecl(const clang::Decl *decl, CoqPrinter &print)
{
  PrintDecl::printer.Visit(decl, print, *this);
}
