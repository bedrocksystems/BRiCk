#include "CoqPrinter.hpp"
#include "ClangPrinter.hpp"
#include "clang/AST/Mangle.h"
#include "clang/AST/Type.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>

using namespace clang;

class PrintStmt
        : public ConstStmtVisitor<PrintStmt, void, CoqPrinter &, ClangPrinter &> {
private:
  PrintStmt() {}
public:
  static PrintStmt printer;

  void VisitStmt(const Stmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.error() << "unsupported statement " << stmt->getStmtClassName()
                  << "\n";
  }

  void VisitDeclStmt(
          const DeclStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Sdecl") << fmt::lparen;
    for (auto i : stmt->decls()) {
      cprint.printLocalDecl(i, print);
      print.output() << fmt::nbsp << "::";
    }
    print.output() << fmt::nbsp << "nil" << fmt::rparen << fmt::rparen;
  }

  void VisitWhileStmt(
          const WhileStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Swhile");
    if (auto v = stmt->getConditionVariable()) {
      print.some();
      cprint.printLocalDecl(v, print);
      print.output() << fmt::rparen;
    } else {
      print.none();
    }
    print.output() << fmt::nbsp;
    cprint.printExpr(stmt->getCond(), print);
    print.output() << fmt::nbsp;
    cprint.printStmt(stmt->getBody(), print);
    print.output() << fmt::rparen;
  }

  void VisitForStmt(
          const ForStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Sfor");
    if (auto v = stmt->getInit()) {
      print.some();
      cprint.printStmt(v, print);
      print.output() << fmt::rparen;
    } else {
      print.none();
    }
    print.output() << fmt::nbsp;
    if (auto v = stmt->getCond()) {
      print.some();
      cprint.printExpr(v, print);
      print.output() << fmt::rparen;
    } else {
      print.none();
    }
    print.output() << fmt::nbsp;
    if (auto v = stmt->getInc()) {
      print.some();
      cprint.printExprAndValCat(v, print);
      print.output() << fmt::rparen;
    } else {
      print.none();
    }
    print.output() << fmt::nbsp;
    cprint.printStmt(stmt->getBody(), print);
    print.output() << fmt::rparen;
  }

  void VisitDoStmt(const DoStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Sdo");
    cprint.printStmt(stmt->getBody(), print);
    print.output() << fmt::nbsp;
    cprint.printExpr(stmt->getCond(), print);
    print.output() << fmt::rparen;
  }

  void VisitBreakStmt(
          const BreakStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.output() << "Sbreak";
  }

  void VisitContinueStmt(
          const ContinueStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.output() << "Scontinue";
  }

  void VisitIfStmt(const IfStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Sif");
    if (auto v = stmt->getConditionVariable()) {
      print.some();
      cprint.printLocalDecl(v, print);
      print.output() << fmt::rparen;
    } else {
      print.none();
    }
    print.output() << fmt::nbsp;
    cprint.printExpr(stmt->getCond(), print);
    print.output() << fmt::nbsp;
    cprint.printStmt(stmt->getThen(), print);
    print.output() << fmt::nbsp;
    if (stmt->getElse()) {
      cprint.printStmt(stmt->getElse(), print);
    } else {
      print.output() << "Sskip";
    }
    print.output() << fmt::rparen;
  }

  void VisitSwitchStmt(
          const SwitchStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Sswitch");
    cprint.printExpr(stmt->getCond(), print);
    const SwitchCase *sc = stmt->getSwitchCaseList();
    print.output() << fmt::lparen;
    while (sc) {
      print.output() << fmt::lparen;
      if (isa<DefaultStmt>(sc)) {
        print.output() << "Default";
      } else if (auto cs = dyn_cast<CaseStmt>(sc)) {
        if (cs->getRHS()) {
          print.output() << "Range" << fmt::nbsp;
          cprint.printExpr(cs->getLHS(), print);
          print.output() << fmt::nbsp;
          cprint.printExpr(cs->getRHS(), print);
        } else {
          print.output() << "Exact" << fmt::nbsp;
          cprint.printExpr(cs->getLHS(), print);
        }
      } else {
        print.error() << "switch body not default or case.\n";
        llvm::errs().flush();
        assert(false);
      }
      print.output() << "," << fmt::nbsp;
      cprint.printStmt(sc->getSubStmt(), print);
      print.output() << fmt::rparen;

      sc = sc->getNextSwitchCase();
    }
    print.output() << "::nil" << fmt::rparen << fmt::rparen;
  }

  void VisitExpr(const Expr *expr, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Sexpr");
    cprint.printValCat(expr, print);
    print.output() << fmt::nbsp;
    cprint.printExpr(expr, print);
    print.output() << fmt::rparen;
  }

  void VisitReturnStmt(
          const ReturnStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    if (stmt->getRetValue() != nullptr) {
      print.ctor("Sreturn (Some") << "(";
      cprint.printValCat(stmt->getRetValue(), print);
      print.output() << "," << fmt::nbsp;
      cprint.printExpr(stmt->getRetValue(), print);
      print.output() << "))" << fmt::rparen;
    } else {
      print.output() << "(Sreturn None)";
    }
  }

  void VisitCompoundStmt(
          const CompoundStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.ctor("Sseq") << fmt::lparen;
    for (auto i : stmt->body()) {
      cprint.printStmt(i, print);
      print.output() << "::";
    }
    print.output() << "nil" << fmt::rparen << fmt::rparen;
  }

  void VisitNullStmt(
          const NullStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    print.output() << "Sskip";
  }

  void VisitGCCAsmStmt(
          const GCCAsmStmt *stmt, CoqPrinter &print, ClangPrinter &cprint)
  {
    // todo(gmm): more to do here to support assembly
    print.ctor("Sasm") << "\"" << stmt->getAsmString()->getString() << "\"";
    print.output() << fmt::rparen;
  }
};

PrintStmt PrintStmt::printer;


void ClangPrinter::printStmt(const clang::Stmt *stmt, CoqPrinter &print)
{
  PrintStmt::printer.Visit(stmt, print, *this);
}