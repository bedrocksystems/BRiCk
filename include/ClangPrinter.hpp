/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include <clang/Basic/Diagnostic.h>
#include <llvm/ADT/Optional.h>

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
class SourceRange;
class CompilerInstance;
class Sema;
class TypeDecl;
}

class CoqPrinter;
class OpaqueNames;

class ClangPrinter {
public:
    bool printDecl(const clang::Decl* d, CoqPrinter& print);

    bool printLocalDecl(const clang::Decl* d, CoqPrinter& print);

    void printStmt(const clang::Stmt* s, CoqPrinter& print);

    void printType(const clang::Type* t, CoqPrinter& print);

    void printExpr(const clang::Expr* d, CoqPrinter& print);
    void printExpr(const clang::Expr* d, CoqPrinter& print, OpaqueNames& li);

    void printValCat(const clang::Expr* d, CoqPrinter& print);

    // Print value name
    void printObjName(const clang::NamedDecl* decl, CoqPrinter& print,
                      bool raw = false);
    void printTypeName(const clang::TypeDecl* decl, CoqPrinter& print);

    void printName(const clang::ValueDecl* decl, CoqPrinter& print);

    void printParamName(const clang::ParmVarDecl* d, CoqPrinter& print);

    // Printing types
    void printQualType(const clang::QualType& qt, CoqPrinter& print);

    void printQualifier(const clang::QualType& qt, CoqPrinter& print) const;

    void printQualifier(bool is_const, bool is_volatile,
                        CoqPrinter& print) const;

    void printExprAndValCat(const clang::Expr* expr, CoqPrinter& print);
    void printExprAndValCat(const clang::Expr* expr, CoqPrinter& print,
                            OpaqueNames&);

    void printField(const clang::ValueDecl*, CoqPrinter&);

    void printCallingConv(clang::CallingConv, CoqPrinter&);

    unsigned getTypeSize(const clang::BuiltinType* type) const;

    std::string sourceRange(const clang::SourceRange sr) const;

    llvm::Optional<int> getParameterNumber(const clang::ParmVarDecl* decl);

    ClangPrinter(clang::CompilerInstance* compiler, clang::ASTContext* context);

    clang::Sema& getSema() const;

    const clang::ASTContext& getContext() const {
        return *context_;
    }

private:
    clang::CompilerInstance* compiler_;
    clang::ASTContext* context_;
    clang::MangleContext* mangleContext_;
    // clang::DiagnosticsEngine engine_;
};
