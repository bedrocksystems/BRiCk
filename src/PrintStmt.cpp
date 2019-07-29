/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "clang/AST/Mangle.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.inc"

using namespace clang;

class PrintStmt :
    public ConstStmtVisitor<PrintStmt, void, CoqPrinter &, ClangPrinter &,
                            ASTContext &> {
private:
    PrintStmt() {}

public:
    static PrintStmt printer;

    void VisitStmt(const Stmt *stmt, CoqPrinter &print, ClangPrinter &cprint,
                   ASTContext &) {
        using namespace logging;
        fatal() << "unsupported statement " << stmt->getStmtClassName() << "\n";
        die();
    }

    void VisitDeclStmt(const DeclStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sdecl") << fmt::lparen;
        for (auto i : stmt->decls()) {
            if (auto sl = dyn_cast<VarDecl>(i)) {
                if (sl->isStaticLocal()) {
                    continue;
                }
            }
            cprint.printLocalDecl(i, print);
            print.output() << fmt::nbsp << "::";
        }
        print.output() << fmt::nbsp << "nil" << fmt::rparen << fmt::rparen;
    }

    void VisitWhileStmt(const WhileStmt *stmt, CoqPrinter &print,
                        ClangPrinter &cprint, ASTContext &) {
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

    void VisitForStmt(const ForStmt *stmt, CoqPrinter &print,
                      ClangPrinter &cprint, ASTContext &) {
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

    void VisitDoStmt(const DoStmt *stmt, CoqPrinter &print,
                     ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sdo");
        cprint.printStmt(stmt->getBody(), print);
        print.output() << fmt::nbsp;
        cprint.printExpr(stmt->getCond(), print);
        print.output() << fmt::rparen;
    }

    void VisitBreakStmt(const BreakStmt *stmt, CoqPrinter &print,
                        ClangPrinter &cprint, ASTContext &) {
        print.output() << "Sbreak";
    }

    void VisitContinueStmt(const ContinueStmt *stmt, CoqPrinter &print,
                           ClangPrinter &cprint, ASTContext &) {
        print.output() << "Scontinue";
    }

    void VisitIfStmt(const IfStmt *stmt, CoqPrinter &print,
                     ClangPrinter &cprint, ASTContext &) {
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

    void VisitCaseStmt(const CaseStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &ctxt) {
        // note, this only occurs when printing the body of a switch statement
        print.ctor("Scase");

        if (stmt->getRHS()) {
            print.ctor("Range", false)
                << stmt->getLHS()->EvaluateKnownConstInt(ctxt) << "%Z"
                << fmt::nbsp << stmt->getRHS()->EvaluateKnownConstInt(ctxt)
                << "%Z";
            print.end_ctor();
        } else {
            print.ctor("Exact", false)
                << stmt->getLHS()->EvaluateKnownConstInt(ctxt) << "%Z";
            print.end_ctor();
        }

        print.end_ctor();

        print.cons();

        cprint.printStmt(stmt->getSubStmt(), print);
    }

    void VisitDefaultStmt(const DefaultStmt *stmt, CoqPrinter &print,
                          ClangPrinter &cprint, ASTContext &) {
        print.output() << "Sdefault";
    }

    void VisitSwitchStmt(const SwitchStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sswitch");
        cprint.printExpr(stmt->getCond(), print);

        cprint.printStmt(stmt->getBody(), print);
        print.end_ctor();
    }

    void VisitExpr(const Expr *expr, CoqPrinter &print, ClangPrinter &cprint,
                   ASTContext &) {
        print.ctor("Sexpr");
        cprint.printValCat(expr, print);
        print.output() << fmt::nbsp;
        cprint.printExpr(expr, print);
        print.output() << fmt::rparen;
    }

    void VisitReturnStmt(const ReturnStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
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

    void VisitCompoundStmt(const CompoundStmt *stmt, CoqPrinter &print,
                           ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sseq");
        print.begin_list();
        for (auto i : stmt->body()) {
            cprint.printStmt(i, print);
            print.cons();
        }
        print.end_list();
        print.end_ctor();
    }

    void VisitNullStmt(const NullStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        print.output() << "Sskip";
    }

    void VisitGCCAsmStmt(const GCCAsmStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        // todo(gmm): more to do here to support assembly
        print.ctor("Sasm");
        print.str(stmt->getAsmString()->getString()) << fmt::nbsp;

        print.output() << (stmt->isVolatile() ? "true" : "false") << fmt::nbsp;

        // inputs
        print.begin_list();
        for (unsigned i = 0; i < stmt->getNumInputs(); ++i) {
            print.begin_tuple();
            print.str(stmt->getInputConstraint(i));
            print.next_tuple();
            cprint.printExpr(stmt->getInputExpr(i), print);
            print.end_tuple();
            print.cons();
        }
        print.end_list();

        // outputs
        print.begin_list();
        for (unsigned i = 0; i < stmt->getNumOutputs(); ++i) {
            print.begin_tuple();
            print.str(stmt->getOutputConstraint(i));
            print.next_tuple();
            cprint.printExpr(stmt->getOutputExpr(i), print);
            print.end_tuple();
            print.cons();
        }
        print.end_list();

        // clobbers
        print.begin_list();
        for (unsigned i = 0; i < stmt->getNumClobbers(); ++i) {
            print.str(stmt->getClobber(i));
            print.cons();
        }
        print.end_list();

        print.output() << fmt::rparen;
    }

    void VisitAttributedStmt(const clang::AttributedStmt *stmt,
                             CoqPrinter &print, ClangPrinter &cprint,
                             ASTContext &) {

        print.ctor("Sattr");
        print.begin_list();
        for (auto i : stmt->getAttrs()) {
            print.str(i->getSpelling());
            print.cons();
        }
        print.end_list();

        cprint.printStmt(stmt->getSubStmt(), print);

        print.end_ctor();
    }
};

PrintStmt PrintStmt::printer;

void
ClangPrinter::printStmt(const clang::Stmt *stmt, CoqPrinter &print) {
    auto depth = print.output().get_depth();
    PrintStmt::printer.Visit(stmt, print, *this, *this->context_);
    assert(depth == print.output().get_depth());
}
