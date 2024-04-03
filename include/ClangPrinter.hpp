/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include "Location.hpp"
#include "Logging.hpp"
#include "Trace.hpp"
#include <clang/Basic/Diagnostic.h>
#include <llvm/ADT/ArrayRef.h>

namespace clang {
class Decl;
class Stmt;
class Expr;
class NamedDecl;
class QualType;
class FunctionDecl;
enum OverloadedOperatorKind : int;
class TranslationUnitDecl;
class ParmVarDecl;
class Type;
class BuiltinType;
class DecltypeType;
class ASTContext;
class MangleContext;
class ValueDecl;
class SourceRange;
class CompilerInstance;
class Sema;
class TypeDecl;
class RecordDecl;
class DeclContext;
class TemplateDecl;
class TemplateParameterList;
class TemplateArgument;
class TemplateArgumentLoc;
class TemplateArgumentList;
}

namespace fmt {
class Formatter;
}

// TODO: The following are misplaced
/*
A reference to a `T` that is less error-prone than `T&`.

Example: To safely call a function `const DeclContext& f()`, one must
wite `auto& ctx = f();` rather than `auto ctx = f();`. The latter
results in a declaration context `ctx` which _does not_ satisfy clang's
invariants and readily leads to segmentation violations and other bad
symptoms. Returning `ref<const DeclContext>` avoids this foot gun.
*/
template<typename T>
class ref final {
private:
	T& ref_;
	ref() = delete;

public:
	explicit ref(T& r) : ref_{r} {}

	operator T&() const {
		return ref_;
	}

	using type = typename std::remove_reference<T>::type;
	type* operator->() const {
		return &ref_;
	}
};
template<typename T>
explicit ref(T&) -> ref<T>;

/*
C++23 permits attributes in a closure to decorate its operator().
To avoid a compiler warning, we instead use gcc's attribute syntax.
Attribution: https://stackoverflow.com/a/70991613
*/
#define NORETURN __attribute__((__noreturn__))
#define NODISCARD __attribute__((__warn_unused_result__))

class CoqPrinter;
struct OpaqueNames;

bool is_dependent(const clang::Expr*);

/**
If `decl` is a template, produce its template declaration.
*/
const clang::TemplateDecl* recoverTemplate(const clang::Decl&);

/**
Find the declaration that was specialized to produced `decl`, avoiding
intermediate template specializations.

This can fail for special member functions.
*/
const clang::NamedDecl* recoverPattern(const clang::Decl&);

class ClangPrinter {
private:
	clang::CompilerInstance* compiler_;
	clang::ASTContext* context_;
	clang::MangleContext* mangleContext_;
	const Trace::Mask trace_;
	const clang::DeclContext* decl_{nullptr};

	ClangPrinter(const ClangPrinter& from, const clang::DeclContext* decl)
		: compiler_(from.compiler_), context_(from.context_),
		  mangleContext_(from.mangleContext_), trace_(from.trace_),
		  decl_{decl} {}

public:
	// Silence some warnings until we can improve our diagnostics
	static inline constexpr bool warn_well_known = false;

	// Make `--trace` output more verbose
	static inline constexpr bool debug = false;

	ClangPrinter(clang::CompilerInstance* compiler, clang::ASTContext* context,
				 Trace::Mask trace);

	/*
    This declaration provides context for resolving template
    argument names and for diagnostics (e.g., an approximate
    source location for type-related warnings).
    */
	ClangPrinter withDecl(const clang::DeclContext* d) const {
		return {*this, d};
	}

private:
	const clang::Decl* getDecl() const;

public:
	clang::ASTContext& getContext() {
		return *context_;
	}

	clang::CompilerInstance& getCompiler() {
		return *compiler_;
	}

	clang::MangleContext& getMangleContext() {
		return *mangleContext_;
	}

	// Helpers for diagnostics
	llvm::raw_ostream& debug_dump(loc::loc);
	llvm::raw_ostream& error_prefix(llvm::raw_ostream&, loc::loc);

	std::string sourceLocation(const clang::SourceLocation) const;
	std::string sourceRange(const clang::SourceRange sr) const;

	// Helpers for `--trace`
	bool trace(Trace::Mask m) const {
		return trace_ & m;
	}
	llvm::raw_ostream& trace(llvm::StringRef whence, loc::loc);

	// Names, respecting --ast2

	fmt::Formatter& printUnsupportedName(llvm::StringRef, CoqPrinter&);
	fmt::Formatter& printTypeName(const clang::TypeDecl& decl,
								  CoqPrinter& print);
	fmt::Formatter& printTypeName(const clang::TypeDecl* decl,
								  CoqPrinter& print, loc::loc);
	fmt::Formatter& printDtorName(const clang::CXXRecordDecl&, CoqPrinter&);
	fmt::Formatter& printObjName(const clang::ValueDecl& decl,
								 CoqPrinter& print);
	fmt::Formatter& printObjName(const clang::ValueDecl* decl,
								 CoqPrinter& print, loc::loc);

	// Print all parameters in scope; for example, with
	// `template<typename T> struct s{ int x; template<typename U> void
	// f(T, U); };`, emits roughly `<T>` for `s` and `<T,U>` for `s::f`.
	// With `as_arg`, print template arguments synthesized from parameters.
	fmt::Formatter& printTemplateParameters(const clang::Decl&, CoqPrinter&,
											bool as_arg = false);

	fmt::Formatter&
	printTemplateArgumentList(const clang::TemplateArgumentList&, CoqPrinter&,
							  loc::loc);
	fmt::Formatter&
	printTemplateArgumentList(llvm::ArrayRef<clang::TemplateArgument>,
							  CoqPrinter&);
	fmt::Formatter&
	printTemplateArgumentList(llvm::ArrayRef<clang::TemplateArgumentLoc>,
							  CoqPrinter&);

	// Print all arguments in scope
	fmt::Formatter& printTemplateArguments(const clang::Decl&, CoqPrinter&);

	// Names, ignoring --ast2

	fmt::Formatter& printNameComment(const clang::Decl&, CoqPrinter&);
	fmt::Formatter& printStructuredName(const clang::Decl&,
										CoqPrinter&);				   // : name
	fmt::Formatter& printMangledName(const clang::Decl&, CoqPrinter&); // : bs
	fmt::Formatter& printMangledTypeName(const clang::TypeDecl&,
										 CoqPrinter&); // : bs
	fmt::Formatter& printMangledTypeName(const clang::TypeDecl*, CoqPrinter&,
										 loc::loc);
	fmt::Formatter& printMangledObjName(const clang::ValueDecl&,
										CoqPrinter&); // : bs
	fmt::Formatter& printMangledObjName(const clang::ValueDecl*, CoqPrinter&,
										loc::loc);
	fmt::Formatter& printUnqualifiedName(const clang::NamedDecl&,
										 CoqPrinter&); // : bs
	fmt::Formatter& printUnqualifiedName(const clang::NamedDecl*, CoqPrinter&,
										 loc::loc);

	// TODO: Adjust and use in the structured name printer
	fmt::Formatter& printNameForAnonTemplateParam(unsigned depth,
												  unsigned index,
												  CoqPrinter& print, loc::loc);

	fmt::Formatter& printParamName(const clang::ParmVarDecl* d,
								   CoqPrinter& print);

	fmt::Formatter& printOverloadableOperator(clang::OverloadedOperatorKind,
											  CoqPrinter&, loc::loc);

	// Types

	fmt::Formatter& printQualType(const clang::QualType& qt, CoqPrinter& print,
								  loc::loc loc);
	fmt::Formatter& printQualTypeOption(const clang::QualType& qt,
										CoqPrinter& print, loc::loc loc);

	fmt::Formatter& printType(const clang::Type&, CoqPrinter&);
	fmt::Formatter& printType(const clang::Type* t, CoqPrinter& print,
							  loc::loc);

	fmt::Formatter& printQualifier(bool is_const, bool is_volatile,
								   CoqPrinter& print) const;
	fmt::Formatter& printQualifier(const clang::QualType& qt,
								   CoqPrinter& print) const;

	fmt::Formatter& printValCat(const clang::Expr* d, CoqPrinter& print);

	fmt::Formatter& printCallingConv(clang::CallingConv, CoqPrinter&, loc::loc);
	fmt::Formatter& printCallingConv(const clang::FunctionDecl&, CoqPrinter&);

	fmt::Formatter& printVariadic(bool, CoqPrinter&) const;

	unsigned getTypeSize(const clang::BuiltinType* type) const;

	// Expressions

	fmt::Formatter& printExpr(const clang::Expr* d, CoqPrinter& print,
							  OpaqueNames& li);
	fmt::Formatter& printExpr(const clang::Expr* d, CoqPrinter& print);

	fmt::Formatter& printValueDeclExpr(const clang::ValueDecl*,
									   CoqPrinter& print, OpaqueNames&);
	fmt::Formatter& printValueDeclExpr(const clang::ValueDecl*,
									   CoqPrinter& print);

	// Statements

	fmt::Formatter& printStmt(const clang::Stmt* s, CoqPrinter& print);

	// true if printed
	bool printLocalDecl(const clang::Decl* d, CoqPrinter& print);

	// Declarations

	// true if printed
	bool printDecl(const clang::Decl* d, CoqPrinter& print);

	// Notation

	fmt::Formatter& printField(const clang::ValueDecl*, CoqPrinter&);
};
