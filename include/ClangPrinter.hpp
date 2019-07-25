/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#pragma once
#include <clang/Basic/Diagnostic.h>

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
class BuiltinType;
class ASTContext;
class MangleContext;
class ValueDecl;
}

class CoqPrinter;

class ClangPrinter {
public:
    void printDecl(const clang::Decl* d, CoqPrinter& print);

    void printParam(const clang::ParmVarDecl* d, CoqPrinter& print);

    void printLocalDecl(const clang::Decl* d, CoqPrinter& print);

    void printStmt(const clang::Stmt* s, CoqPrinter& print);

    void printType(const clang::Type* t, CoqPrinter& print);

    void printExpr(const clang::Expr* d, CoqPrinter& print);

    void printValCat(const clang::Expr* d, CoqPrinter& print);

    void printGlobalName(const clang::NamedDecl* decl, CoqPrinter& print,
                         bool raw = false);

    void printName(const clang::NamedDecl* decl, CoqPrinter& print);

    void printQualType(const clang::QualType& qt, CoqPrinter& print);

    void printQualifier(const clang::QualType& qt, CoqPrinter& print) const;

    void printQualifier(bool is_const, bool is_volatile,
                        CoqPrinter& print) const;

    void printExprAndValCat(const clang::Expr* expr, CoqPrinter& print);

    void printField(const clang::ValueDecl*, CoqPrinter&);

    unsigned getTypeSize(const clang::BuiltinType* type) const;

    ClangPrinter(clang::ASTContext* context);

private:
    clang::ASTContext* context_;
    clang::MangleContext* mangleContext_;
    clang::DiagnosticsEngine engine_;
};