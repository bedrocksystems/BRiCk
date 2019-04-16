/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include <list>
#include <Formatter.hpp>
#include "clang/Basic/Version.inc"
#include "clang/AST/Type.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Mangle.h"
#include "TypeVisitorWithArgs.h"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "CommentScanner.hpp"
#include "SpecCollector.hpp"

using namespace clang;
using namespace fmt;

__attribute__((noreturn))
void fatal(StringRef msg) {
	llvm::errs() << "[FATAL ERROR] " << msg << "\n";
	llvm::errs().flush();
	exit(1);
}

#if 0
class ToCoq {
private:
	Formatter &out;
	DiagnosticsEngine engine;


private:
	PrintLocalDecl localPrinter;
	PrintDecl declPrinter;
	Filter *const filter;
	SpecCollector& specifications;

public:
	explicit
	ToCoq(ASTContext *ctxt, Formatter &fmt, Filter *f, SpecCollector &specs)
	: out(fmt), engine(IntrusiveRefCntPtr<DiagnosticIDs>(), IntrusiveRefCntPtr<DiagnosticOptions>()), localPrinter(this), declPrinter(this), filter(f), specifications(specs), Context(ctxt) {
		mangleContext = ItaniumMangleContext::create(*ctxt, engine);

	}

	SourceLocation
	getStartSourceLocWithComment(const Decl* d) {
		if (auto comment = Context->getRawCommentForDeclNoCache(d)) {
			return comment->getLocStart();
		} else {
			return d->getLocStart();
		}
	}

	Decl*
	getPreviousDeclInContext(const Decl* d) {
		auto dc = d->getLexicalDeclContext();

		Decl* prev = nullptr;
		for (auto it : dc->decls()) {
			if (it == d) {
				return prev;
			} else {
				prev = it;
			}
		}
		return nullptr;
	}

	SourceLocation
	getPrevSourceLoc(const Decl* d) {
		SourceManager &sm = Context->getSourceManager();
		auto pd = getPreviousDeclInContext(d);
		if (pd && pd->getLocEnd().isValid()) {
			return pd->getLocEnd();
		} else {
			return sm.getLocForStartOfFile(sm.getFileID(d->getSourceRange().getBegin()));
		}
	}

	bool
	printDecl (const Decl* d) {
		SourceManager &sm = Context->getSourceManager();
		auto start = getPrevSourceLoc(d);
		auto end = getStartSourceLocWithComment(d);
		if (start.isValid() && end.isValid()) {
			comment::CommentScanner comments(StringRef(sm.getCharacterData(start), sm.getCharacterData(end) - sm.getCharacterData(start)));
			StringRef comment;
			while (comments.next(comment)) {
				error() << "comment:\n";
				error() << comment << "\n";
			}
		}

		Filter::What what = filter->shouldInclude(d);
		if (what != Filter::What::NOTHING) {
			return declPrinter.Visit(d, what);
		}
		return false;
	}




	

	void
	printQualType(const QualType &qt) {
		if (qt.isLocalConstQualified()) {
			if (qt.isVolatileQualified()) {
				ctor("Qconst_volatile");
			} else {
				ctor("Qconst");
			}
		} else {
			if (qt.isLocalVolatileQualified()) {
				ctor("Qmut_volatile");
			} else {
				ctor("Qmut");
			}
		}
		printType(qt.getTypePtr());
		output() << fmt::rparen;
	}




private:
	ASTContext *Context;
};
#endif

#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"

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

	Formatter fmt(llvm::outs());

	fmt << "From Cpp Require Import Parser." << fmt::line << fmt::line
			<< "Local Open Scope string_scope." << fmt::line
			<< "Import ListNotations." << fmt::line;

	SpecCollector specs;

	CoqPrinter print(fmt);
	ClangPrinter cprint(ctxt);
	translateModule(decl, print, cprint);
}

