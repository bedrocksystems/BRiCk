/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#pragma once

namespace clang {
class Decl;
class Stmt;
class Expr;
class NamedDecl;
class QualType;
class FunctionDecl;
class TranslationUnitDecl;
class ParmVarDecl;
class Type;
}

class CoqPrinter;

using namespace clang;

void declToCoq(clang::ASTContext *ctxt, const clang::Decl *decl);

void stmtToCoq(clang::ASTContext *ctxt, const clang::Stmt *stmt);

void toCoqModule(clang::ASTContext *ctxt,
		const clang::TranslationUnitDecl *decl);


class ClangPrinter {
public:
	void
	printDecl (const Decl* d, CoqPrinter& print);

	void
	printParam (const ParmVarDecl* d, CoqPrinter& print);

	void
	printLocalDecl (const Decl* d, CoqPrinter& print);

	void
	printStmt (const Stmt* s, CoqPrinter& print);

	void
	printType (const Type* t, CoqPrinter& print);

	void
	printExpr (const Expr* d, CoqPrinter& print);

	void
	printValCat(const Expr* d, CoqPrinter& print);

	void
	printGlobalName(const NamedDecl *decl, CoqPrinter& print);

	void
	printName(const NamedDecl *decl, CoqPrinter& print);

	void
	printQualType(const QualType &qt, CoqPrinter& print);

	void
	printFunction(const FunctionDecl *decl, CoqPrinter& print);

	void
	printExprAndValCat(const Expr *expr, CoqPrinter& print);

/*
	void
	printMethod(const CXXMethodDecl *decl, CoqPrinter& print);

	void
	printConstructor(const CXXConstructorDecl *decl, CoqPrinter& print);

	void
	printDestructor(const CXXDestructorDecl *decl, CoqPrinter& print);
*/

	unsigned getCharWidth() const;

	ClangPrinter(clang::ASTContext* context):context_(context) {}

private:
	clang::ASTContext * const context_;
};