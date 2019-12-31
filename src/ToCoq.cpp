/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include "ClangPrinter.hpp"
#include "CommentScanner.hpp"
#include "CoqPrinter.hpp"
#include "Filter.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>
#include <list>

using namespace clang;
using namespace fmt;

#if 0
void declToCoq(ASTContext *ctxt, const clang::Decl* decl) {
	Formatter fmt(llvm::outs());
	Default filter(Filter::What::DEFINITION);
	SpecCollector specs;
	CoqPrinter cprint(fmt);
	ClangPrinter(ctxt).printDecl(decl, cprint);
}

void stmtToCoq(ASTContext *ctxt, const clang::Stmt* stmt) {
	Formatter fmt(llvm::outs());
	Default filter(Filter::What::DEFINITION);
	SpecCollector specs;
	CoqPrinter cprint(fmt);
	ClangPrinter(ctxt).printStmt(stmt, cprint);
}


void
translateModule(const TranslationUnitDecl* decl, CoqPrinter& print, ClangPrinter& cprint) {
	print.output() << "Definition module : list Decl :=" << fmt::indent << fmt::line;
	for (auto i : decl->decls()) {
		cprint.printDecl(i, print);
		print.output() << fmt::line << "::" << fmt::nbsp;
	}
	print.output() << "nil." << fmt::outdent;
	print.output() << fmt::line;
}
#endif

#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"

// Declares clang::SyntaxOnlyAction.
#include "clang/Frontend/FrontendActions.h"

#include "SpecCollector.hpp"
#include "ToCoq.hpp"

using namespace clang;

void
ToCoqConsumer::toCoqModule(clang::ASTContext *ctxt,
                           const clang::TranslationUnitDecl *decl) {
#if 0
	NoInclude noInclude(ctxt->getSourceManager());
	FromComment fromComment(ctxt);
	std::list<Filter*> filters;
	filters.push_back(&noInclude);
	filters.push_back(&fromComment);
	Combine<Filter::What::NOTHING, Filter::max> filter(filters);
#endif
    SpecCollector specs;
    Default filter(Filter::What::DEFINITION);

    ::Module mod;

    build_module(decl, mod, filter, specs);

    if (output_file_.hasValue()) {
        std::error_code ec;
        llvm::raw_fd_ostream code_output(*output_file_, ec);
        if (ec.value()) {
            llvm::errs() << "Failed to open generation file: " << *output_file_
                         << "\n"
                         << ec.message() << "\n";
        } else {
            Formatter fmt(code_output);
            CoqPrinter print(fmt);
            ClangPrinter cprint(ctxt);

            fmt << "Require Import bedrock.lang.cpp.parser." << fmt::line << fmt::line
                << "Local Open Scope string_scope." << fmt::line
                << "Import ListNotations." << fmt::line;

            fmt << fmt::line
                << "Definition module : compilation_unit := " << fmt::indent
                << fmt::line << "Eval reduce_compilation_unit in decls"
                << fmt::nbsp;

            print.begin_list();
            for (auto entry : mod.imports()) {
                auto decl = entry.second.first;
                cprint.printDecl(decl, print);
                print.cons();
            }
            for (auto entry : mod.definitions()) {
                auto decl = entry.second;
                cprint.printDecl(decl, print);
                print.cons();
            }
            print.end_list();
            print.output() << "." << fmt::outdent << fmt::line;
        }
    }

    if (notations_file_.hasValue()) {
        std::error_code ec;
        llvm::raw_fd_ostream notations_output(*notations_file_, ec);
        if (ec.value()) {
            llvm::errs() << "Failed to open notations file: "
                         << *notations_file_ << "\n"
                         << ec.message() << "\n";
        } else {
            fmt::Formatter spec_fmt(notations_output);
            auto &ctxt = decl->getASTContext();
            ClangPrinter cprint(&decl->getASTContext());
            CoqPrinter print(spec_fmt);
            // PrintSpec printer(ctxt);

            NoInclude source(ctxt.getSourceManager());

            print.output() << "(*" << fmt::line
                           << " * Notations extracted from "
                           << ctxt.getSourceManager()
                                  .getFileEntryForID(
                                      ctxt.getSourceManager().getMainFileID())
                                  ->getName()
                           << fmt::line << " *)" << fmt::line
                           << "Require Import bedrock.lang.cpp.parser." << fmt::line
                           << fmt::line;

            // generate all of the record fields
            write_globals(mod, print, cprint);
        }
    }

    if (spec_file_.hasValue()) {
        std::error_code ec;
        llvm::raw_fd_ostream spec_output(*spec_file_, ec);
        if (ec.value()) {
            llvm::errs() << "Failed to open specification file: " << *spec_file_
                         << "\n"
                         << ec.message() << "\n";
        } else {
            fmt::Formatter spec_fmt(spec_output);
            write_spec(&mod, specs, decl, filter, spec_fmt);
        }
    }
}
