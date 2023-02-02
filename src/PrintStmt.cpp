/*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "clang/AST/Mangle.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.inc"
#if CLANG_VERSION_MAJOR >= 10
#include "clang/AST/Attr.h"
#endif

using namespace clang;

class PrintStmt :
    public ConstStmtVisitor<PrintStmt, void, CoqPrinter &, ClangPrinter &,
                            ASTContext &> {
private:
    PrintStmt() {}

public:
    static PrintStmt printer;

    void VisitStmt(const Stmt *stmt, CoqPrinter &print, ClangPrinter &cprint,
                   ASTContext &ctxt) {
        using namespace logging;
        fatal() << "unsupported statement " << stmt->getStmtClassName()
                << " at "
                << stmt->getSourceRange().printToString(ctxt.getSourceManager())
                << "\n";
        die();
    }

    void VisitDeclStmt(const DeclStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sdecl");
        print.begin_list();
        for (auto d : stmt->decls()) {
            if (cprint.printLocalDecl(d, print))
                print.cons();
        }
        print.end_list();
        print.end_ctor();
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
        print.end_ctor();
    }

    void VisitForStmt(const ForStmt *stmt, CoqPrinter &print,
                      ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sfor");
        if (auto v = stmt->getInit()) {
            print.some();
            cprint.printStmt(v, print);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;
        if (auto v = stmt->getCond()) {
            print.some();
            cprint.printExpr(v, print);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;
        if (auto v = stmt->getInc()) {
            print.some();
            cprint.printExpr(v, print);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;
        cprint.printStmt(stmt->getBody(), print);
        print.end_ctor();
    }

    void VisitCXXForRangeStmt(const CXXForRangeStmt *stmt, CoqPrinter &print,
                              ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sforeach");
        cprint.printStmt(stmt->getRangeStmt(), print);
        print.output() << fmt::nbsp;
        cprint.printStmt(stmt->getBeginStmt(), print);
        print.output() << fmt::nbsp;
        cprint.printStmt(stmt->getEndStmt(), print);
        print.output() << fmt::nbsp;
        if (auto v = stmt->getInit()) {
            print.some();
            cprint.printStmt(v, print);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;
        if (auto v = stmt->getCond()) {
            print.some();
            cprint.printExpr(v, print);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;
        if (auto v = stmt->getInc()) {
            print.some();
            cprint.printExpr(v, print);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;
        cprint.printStmt(stmt->getLoopVarStmt(), print);
        print.output() << fmt::nbsp;
        cprint.printStmt(stmt->getBody(), print);
        print.end_ctor();
    }

    void VisitDoStmt(const DoStmt *stmt, CoqPrinter &print,
                     ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sdo");
        cprint.printStmt(stmt->getBody(), print);
        print.output() << fmt::nbsp;
        cprint.printExpr(stmt->getCond(), print);
        print.end_ctor();
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
            print.end_ctor();
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
        print.end_ctor();
    }

    void VisitCaseStmt(const CaseStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &ctxt) {
        // note, this only occurs when printing the body of a switch statement
        print.ctor("Scase");

        if (stmt->getRHS()) {
            print.ctor("Range", false)
                << "(" << stmt->getLHS()->EvaluateKnownConstInt(ctxt) << ")%Z"
                << fmt::nbsp << "("
                << stmt->getRHS()->EvaluateKnownConstInt(ctxt) << ")%Z";
            print.end_ctor();
        } else {
            print.ctor("Exact", false)
                << "(" << stmt->getLHS()->EvaluateKnownConstInt(ctxt) << ")%Z";
            print.end_ctor();
        }

        print.end_ctor();

        print.cons();

        cprint.printStmt(stmt->getSubStmt(), print);
    }

    void VisitDefaultStmt(const DefaultStmt *stmt, CoqPrinter &print,
                          ClangPrinter &cprint, ASTContext &) {
        print.output() << "Sdefault";

        if (stmt->getSubStmt()) {
            print.cons();
            cprint.printStmt(stmt->getSubStmt(), print);
        }
    }

    void VisitSwitchStmt(const SwitchStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sswitch");
        if (auto v = stmt->getConditionVariable()) {
            print.some();
            cprint.printLocalDecl(v, print);
            print.end_ctor();
        } else {
            print.none();
        }
        cprint.printExpr(stmt->getCond(), print);

        cprint.printStmt(stmt->getBody(), print);
        print.end_ctor();
    }

    void VisitExpr(const Expr *expr, CoqPrinter &print, ClangPrinter &cprint,
                   ASTContext &) {
        print.ctor("Sexpr");
        cprint.printExpr(expr, print);
        print.end_ctor();
    }

    void VisitReturnStmt(const ReturnStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        if (auto rv = stmt->getRetValue()) {
            print.ctor("Sreturn_val");
            cprint.printExpr(rv, print);
            print.end_ctor();
        } else {
            print.output() << "Sreturn_void";
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

        print.end_ctor();
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

    void VisitLabelStmt(const LabelStmt *stmt, CoqPrinter &print,
                        ClangPrinter &cprint, ASTContext &) {
        print.ctor("Slabeled");
        print.str(stmt->getDecl()->getNameAsString()) << fmt::nbsp;
        cprint.printStmt(stmt->getSubStmt(), print);
        print.end_ctor();
    }

    void VisitGotoStmt(const GotoStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sgoto");
        print.str(stmt->getLabel()->getNameAsString());
        print.end_ctor();
    }

    void VisitCXXTryStmt(const CXXTryStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sunsupported");
        print.str("try");
        print.end_ctor();
    }
};

PrintStmt PrintStmt::printer;

void
ClangPrinter::printStmt(const clang::Stmt *stmt, CoqPrinter &print) {
    __attribute__((unused)) auto depth = print.output().get_depth();
    PrintStmt::printer.Visit(stmt, print, *this, *this->context_);
    assert(depth == print.output().get_depth());
}
