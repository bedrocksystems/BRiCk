#include <Formatter.hpp>
#include "clang/Basic/Version.inc"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Mangle.h"
#include "TypeVisitorWithArgs.h"
#include "CoqPrinter.hpp"
#include "ClangPrinter.hpp"

using namespace clang;
using namespace fmt;

void
printQualType(const QualType& qt, CoqPrinter& print, ClangPrinter& cprint) {
  if (qt.isLocalConstQualified()) {
    if (qt.isVolatileQualified()) {
      print.ctor("Qconst_volatile");
    } else {
      print.ctor("Qconst");
    }
  } else {
    if (qt.isLocalVolatileQualified()) {
      print.ctor("Qmut_volatile");
    } else {
      print.ctor("Qmut");
    }
  }
  cprint.printType(qt.getTypePtr(), print);
  print.output() << fmt::rparen;
}

class PrintType : public TypeVisitor<PrintType, void, CoqPrinter&, ClangPrinter&> {
private:
  PrintType() {}

public:
  static PrintType printer;

  void VisitType(const Type *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.error() << "[ERR] unsupported type: ";
    type->dump(print.error());
    print.error() << "\n";
    exit(1);
  }

  void VisitAutoType(const AutoType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    cprint.printQualType(type->getDeducedType(), print);
  }

  void VisitTemplateTypeParmType(const TemplateTypeParmType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Ttemplate") << "\"" << type->getDecl()->getNameAsString() << "\""
                      << fmt::rparen;
  }

  void VisitEnumType(const EnumType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Tref", false);
    cprint.printGlobalName(type->getDecl(), print);
    print.output() << fmt::rparen;
  }
  void VisitRecordType(const RecordType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Tref", false);
    cprint.printGlobalName(type->getDecl(), print);
    print.output() << fmt::rparen;
  }

  void VisitParenType(const ParenType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    cprint.printQualType(type->getInnerType(), print);
  }

  void VisitBuiltinType(const BuiltinType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    // todo(gmm): record bitwidths from the context when they are defaulted.
    if (type->getKind() == BuiltinType::Kind::Bool) {
      print.output() << "Tbool";
    } else if (type->getKind() == BuiltinType::Kind::Int128) {
      print.output() << "T_int128";
    } else if (type->getKind() == BuiltinType::Kind::UInt128) {
      print.output() << "T_uint128";
    } else if (type->getKind() == BuiltinType::Kind::Int) {
      print.output() << "T_int";
    } else if (type->getKind() == BuiltinType::Kind::UInt) {
      print.output() << "T_uint";
    } else if (type->getKind() == BuiltinType::Kind::ULong) {
      print.output() << "T_ulong";
    } else if (type->getKind() == BuiltinType::Kind::UShort) {
      print.output() << "T_ushort";
    } else if (type->getKind() == BuiltinType::Kind::Long) {
      print.output() << "T_long";
    } else if (type->getKind() == BuiltinType::Kind::LongDouble) {
      print.output() << "T_long_double";
    } else if (type->getKind() == BuiltinType::Kind::LongLong) {
      print.output() << "T_longlong";
    } else if (type->getKind() == BuiltinType::Kind::ULongLong) {
      print.output() << "T_ulonglong";
    } else if (type->getKind() == BuiltinType::Kind::Short) {
      print.output() << "T_short";
    } else if (type->getKind() == BuiltinType::Kind::Char16) {
      print.output() << "T_char16";
    } else if (type->getKind() == BuiltinType::Kind::Char_S) {
      print.output() << "(Tchar (Some " << cprint.getCharWidth() << ") true)";
    } else if (type->getKind() == BuiltinType::Kind::SChar) {
      print.output() << "(Tchar (Some " << cprint.getCharWidth() << ") true)";
    } else if (type->getKind() == BuiltinType::Kind::UChar) {
      print.output() << "(Tchar (Some " << cprint.getCharWidth() << ") false)";
    } else if (type->getKind() == BuiltinType::Kind::Char_U) {
      print.output() << "(Tchar (Some " << cprint.getCharWidth() << ") false)";
    } else if (type->getKind() == BuiltinType::Kind::Char8) {
      print.output() << "T_char8";
    } else if (type->getKind() == BuiltinType::Kind::Char32) {
      print.output() << "T_char32";
    } else if (type->getKind() == BuiltinType::Kind::Void) {
      print.output() << "Tvoid";
    } else {
      print.error() << "Unsupported type \""
                    << type->getNameAsCString(PrintingPolicy(LangOptions()))
                    << "\"\n";
      llvm::errs().flush();
      exit(1);
    }
  }

  void VisitLValueReferenceType(const LValueReferenceType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Treference");
    printQualType(type->getPointeeType(), print, cprint);
    print.output() << fmt::rparen;
  }

  void VisitRValueReferenceType(const RValueReferenceType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Trv_reference");
    printQualType(type->getPointeeType(), print, cprint);
    print.output() << fmt::rparen;
  }

  void VisitPointerType(const PointerType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Tpointer");
    printQualType(type->getPointeeType(), print, cprint);
    print.output() << fmt::rparen;
  }

  void VisitTypedefType(const TypedefType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Tref", false);
    cprint.printGlobalName(type->getDecl(), print);
    print.output() << fmt::rparen;
  }

  void VisitFunctionProtoType(const FunctionProtoType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Tfunction");
    printQualType(type->getReturnType(), print, cprint);
    print.output() << fmt::nbsp << "[" << fmt::indent;
    for (auto i = type->param_type_begin(), e = type->param_type_end();
            i != e;) {
      printQualType(*i, print, cprint);
      if (++i != e) {
        print.output() << ";" << fmt::nbsp;
      }
    }
    print.output() << "]" << fmt::rparen;
  }

  void VisitElaboratedType(const ElaboratedType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    printQualType(type->getNamedType(), print, cprint);
  }

  void VisitConstantArrayType(const ConstantArrayType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Tarray");
    printQualType(type->getElementType(), print, cprint);
    print.output() << fmt::nbsp << type->getSize().getLimitedValue() << fmt::rparen;
  }

  void VisitSubstTemplateTypeParmType(const SubstTemplateTypeParmType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    printQualType(type->getReplacementType(), print, cprint);
  }

  void VisitIncompleteArrayType(const IncompleteArrayType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    // note(gmm): i might want to note the sugar.
    print.ctor("Qconst");
    print.ctor("Tpointer", false);
    printQualType(type->getElementType(), print, cprint);
    print.output() << fmt::rparen << fmt::rparen;
  }

  void VisitDecayedType(const DecayedType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Qconst");
    print.ctor("Tpointer", false);
    printQualType(type->getPointeeType(), print, cprint);
    print.output() << fmt::rparen << fmt::rparen;
  }

  void VisitTemplateSpecializationType(const TemplateSpecializationType *type, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Tref", false);
    cprint.printGlobalName(type->getAsCXXRecordDecl(), print);
    //cprint.mangleContext->mangleCXXName(type->getAsCXXRecordDecl(), cprint.out.nobreak());
    print.output() << fmt::rparen;
  }
};

PrintType PrintType::printer;

void
ClangPrinter::printType(const clang::Type* type, CoqPrinter& print) {
  PrintType::printer.Visit(type, print, *this);
}

void
ClangPrinter::printQualType(const QualType& qt, CoqPrinter& print) {
  ::printQualType(qt, print, *this);
}