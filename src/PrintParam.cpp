#include "CoqPrinter.hpp"
#include "ClangPrinter.hpp"
#include "clang/AST/Mangle.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.inc"
#include "DeclVisitorWithArgs.h"
#include <Formatter.hpp>

using namespace clang;

class PrintParam : public ConstDeclVisitorArgs<PrintParam, void, CoqPrinter&, ClangPrinter&> {
private:
  PrintParam() {}

public:
  static PrintParam printer;

  void VisitParmVarDecl(const ParmVarDecl *decl, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.output() << fmt::lparen << "\"" << decl->getNameAsString() << "\","
                   << fmt::nbsp;
    cprint.printQualType(decl->getType(), print);
    print.output() << fmt::rparen;
  }

  void VisitDecl(const Decl *decl, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.error() << "unexpected local declaration";
  }
};

PrintParam PrintParam::printer;

void ClangPrinter::printParam(const clang::ParmVarDecl *decl, CoqPrinter &print)
{
  PrintParam::printer.Visit(decl, print, *this);
}