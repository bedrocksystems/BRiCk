/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Logging.hpp"
#include "clang/AST/Mangle.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>

using namespace clang;

class PrintParam :
    public ConstDeclVisitorArgs<PrintParam, void, CoqPrinter&, ClangPrinter&> {
private:
    PrintParam() {}

public:
    static PrintParam printer;

    void VisitParmVarDecl(const ParmVarDecl* decl, CoqPrinter& print,
                          ClangPrinter& cprint) {
        print.output() << fmt::lparen << "\"";
        auto name = decl->getNameAsString();
        if (name != "") {
            print.output() << name;
        } else {
            auto i = cprint.getParameterNumber(decl);
            if (i.hasValue())
                print.output() << "#" << i.getValue();
        }
        print.output() << "\"," << fmt::nbsp;

        cprint.printQualType(decl->getType(), print);
        print.output() << fmt::rparen;
    }

    void VisitDecl(const Decl* decl, CoqPrinter& print, ClangPrinter& cprint) {
        using namespace logging;
        fatal() << "unexpected local declaration while printing parameter "
                << decl->getDeclKindName() << " (at "
                << cprint.sourceRange(decl->getSourceRange()) << ")\n";
        die();
    }
};

PrintParam PrintParam::printer;

void
ClangPrinter::printParam(const clang::ParmVarDecl* decl, CoqPrinter& print) {
    PrintParam::printer.Visit(decl, print, *this);
}
