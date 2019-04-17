/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include <list>
#include <Formatter.hpp>
#include "clang/Basic/Version.inc"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "Filter.hpp"
#include "CommentScanner.hpp"
#include "SpecCollector.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "ModuleBuilder.hpp"

using namespace clang;
using namespace fmt;

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
translateModule (const TranslationUnitDecl* decl, CoqPrinter& print, ClangPrinter& cprint) {
	print.output() << "Definition module : list Decl :=" << fmt::indent << fmt::line;
	for (auto i : decl->decls()) {
		cprint.printDecl(i, print);
		print.output() << fmt::line << "::" << fmt::nbsp;
	}
	print.output() << "nil." << fmt::outdent;
	print.output() << fmt::line;
}

void toCoqModule(clang::ASTContext *ctxt,
		const clang::TranslationUnitDecl *decl) {
	NoInclude noInclude(ctxt->getSourceManager());
	FromComment fromComment(ctxt);
	std::list<Filter*> filters;
	filters.push_back(&noInclude);
	filters.push_back(&fromComment);
	Combine<Filter::What::NOTHING, Filter::max> filter(filters);

	SpecCollector specs;

	::Module mod;

	build_module(decl, mod, filter);

	Formatter fmt(llvm::outs());
	CoqPrinter print(fmt);
	ClangPrinter cprint(ctxt);

	fmt << "From Cpp Require Import Parser." << fmt::line << fmt::line
			<< "Local Open Scope string_scope." << fmt::line
			<< "Import ListNotations." << fmt::line;

#if 0
	fmt << fmt::line
			<< "Definition imports : Ast.module :=" << fmt::indent;
	for (auto entry : mod.imports()) {
		auto decl = entry.second.first;
		cprint.printDecl(decl, print);
		print.output() << fmt::nbsp << "::";
	}
	fmt << "nil." << fmt::outdent << fmt::line;
#endif

	fmt << fmt::line
			<< "Definition module : Ast.module :=" << fmt::indent;

	for (auto entry : mod.definitions()) {
		auto decl = entry.second;
		cprint.printDecl(decl, print);
		print.output() << fmt::nbsp << "::";
	}
	print.output() << "nil." << fmt::outdent << fmt::line;
}

