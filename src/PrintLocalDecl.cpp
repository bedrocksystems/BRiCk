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

using namespace clang;

class PrintLocalDecl :
    public ConstDeclVisitorArgs<PrintLocalDecl, bool, CoqPrinter&,
                                ClangPrinter&> {
private:
    PrintLocalDecl() {}

    static CXXDestructorDecl* get_dtor(QualType qt) {
        if (auto rd = qt->getAsCXXRecordDecl()) {
            return rd->getDestructor();
        } else if (auto ary = qt->getAsArrayTypeUnsafe()) {
            return get_dtor(ary->getElementType());
        } else {
            return nullptr;
        }
    };

public:
    static PrintLocalDecl printer;

    bool VisitVarDecl(const VarDecl* decl, CoqPrinter& print,
                      ClangPrinter& cprint) {
        print.begin_record();
        print.record_field("vd_name")
            << "\"" << decl->getNameAsString() << "\"";

        print.output() << fmt::line << ";";
        print.record_field("vd_type");
        cprint.printQualType(decl->getType(), print);

        print.output() << fmt::line << ";";
        print.record_field("vd_init");
        if (decl->hasInit()) {
            print.ctor("Some", false);
            cprint.printExpr(decl->getInit(), print);
            print.output() << fmt::rparen;
        } else {
            print.none();
        }

        print.output() << fmt::line << ";";
        print.record_field("vd_dtor");
        if (auto dest = get_dtor(decl->getType())) {
            print.some();
            cprint.printGlobalName(dest, print);
            print.end_ctor();
        } else {
            print.none();
        }

        print.end_record();
        return true;
    }

    bool VisitTypeDecl(const TypeDecl* decl, CoqPrinter&,
                       ClangPrinter& cprint) {
        using namespace logging;
        debug() << "local type declarations are (currently) not well supported "
                << decl->getDeclKindName() << " (at "
                << cprint.sourceRange(decl->getSourceRange()) << ")\n";
        return false;
    }

    bool VisitStaticAssertDecl(const StaticAssertDecl* decl, CoqPrinter&,
                               ClangPrinter&) {
        return false;
    }

    bool VisitDecl(const Decl* decl, CoqPrinter& print, ClangPrinter& cprint) {
        using namespace logging;
        debug() << "unexpected local declaration while printing local decl "
                << decl->getDeclKindName() << " (at "
                << cprint.sourceRange(decl->getSourceRange()) << ")\n";
        return false;
    }
};

PrintLocalDecl PrintLocalDecl::printer;

bool
ClangPrinter::printLocalDecl(const clang::Decl* decl, CoqPrinter& print) {
    return PrintLocalDecl::printer.Visit(decl, print, *this);
}
