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

