/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "Assert.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>
#include <clang/Frontend/CompilerInstance.h>
#include <optional>

using namespace clang;

ClangPrinter::ClangPrinter(clang::CompilerInstance *compiler,
						   clang::ASTContext *context, Trace::Mask trace,
						   bool comment)
	: compiler_(compiler), context_(context), trace_(trace), comment_{comment} {
	mangleContext_ =
		ItaniumMangleContext::create(*context, compiler->getDiagnostics());
}

unsigned
ClangPrinter::getTypeSize(const BuiltinType *t) const {
	return this->context_->getTypeSize(t);
}

std::optional<std::pair<const CXXRecordDecl *, clang::Qualifiers>>
ClangPrinter::getLambdaClass() const {
	if (auto md = dyn_cast_or_null<CXXMethodDecl>(getDecl())) {
		auto lambda = md->getParent();
		if (lambda->isLambda()) {
			Qualifiers cv;
			if (md->isConst())
				cv.addConst();
			if (md->isVolatile())
				cv.addVolatile();
			return {{lambda, cv}};
		}
	}
	return std::nullopt;
}

namespace {
std::optional<int>
getParameterNumber(const ParmVarDecl *decl) {
	always_assert(decl->getDeclContext()->isFunctionOrMethod() &&
				  "function or method");
	if (auto fd = dyn_cast_or_null<FunctionDecl>(decl->getDeclContext())) {
		int i = 0;
		for (auto p : fd->parameters()) {
			if (p == decl)
				return std::optional<int>(i);
			++i;
		}
		llvm::errs() << "failed to find parameter\n";
	}
	return std::optional<int>();
}
} // namespace

fmt::Formatter &
ClangPrinter::printParamName(CoqPrinter &print, const ParmVarDecl *decl) {
	if (trace(Trace::Name))
		trace("printParamName", loc::of(decl));

	always_assert(decl->getDeclContext()->isFunctionOrMethod() &&
				  "function or method");
	if (auto fd = dyn_cast_or_null<FunctionDecl>(decl->getDeclContext())) {
		int i = 0;
		clang::IdentifierInfo *info = nullptr;
		unsigned offset = 0;
		for (auto p : fd->parameters()) {
			if (p->getIdentifier() == info) {
				offset++;
			} else
				offset = 0;
			if (p == decl) {
				if (decl->getIdentifier()) {
					print.output() << "\"";
					decl->printName(print.output().nobreak());
					if (offset)
						print.output() << "..." << offset;
					return print.output() << "\"";
				} else {
					return print.output() << "(localname.anon " << i << ")";
				}
			}
			info = p->getIdentifier();
			++i;
		}
	}
	llvm::errs() << "failed to find parameter\n";
	auto loc = loc::of(decl);
	error_prefix(logging::fatal(), loc) << "error: cannot find parameter\n";
	debug_dump(loc);
	logging::die();
	return print.output();
}

fmt::Formatter &
ClangPrinter::printValCat(CoqPrinter &print, const Expr *d) {
	if (trace(Trace::Type))
		trace("printValCat", loc::of(d));

	// note(gmm): Classify doesn't work on dependent types which occur in templates
	// that clang can't completely eliminate.

	if (print.templates()) {
		if (d->isLValue())
			print.output() << "Lvalue";
		else if (d->isPRValue())
			print.output() << "Prvalue";
		else if (d->isXValue())
			print.output() << "Xvalue";
		else {
			auto loc = loc::of(d);
			error_prefix(logging::fatal(), loc)
				<< "error: cannot determine value category\n";
			debug_dump(loc);
			logging::die();
		}
		return print.output();
	}

	auto Class = d->Classify(*this->context_);
	if (Class.isLValue()) {
		print.output() << "Lvalue";
	} else if (Class.isXValue()) {
		print.output() << "Xvalue";
	} else if (Class.isPRValue()) {
		print.output() << "Prvalue";
	} else {
		always_assert(false);
		//fatal("unknown value category");
	}
	return print.output();
}

fmt::Formatter &
ClangPrinter::printTypeTemplateParam(CoqPrinter &print, unsigned depth,
									 unsigned index, loc::loc loc) {
	if (trace(Trace::Name))
		trace("printTypeTemplateParam", loc);

	for (auto d = decl_; d; d = d->getLexicalParent()) {
		if (auto psd = dyn_cast<ClassTemplatePartialSpecializationDecl>(d)) {
			for (auto i : psd->getTemplateParameters()->asArray()) {
				if (auto tpd = dyn_cast<TemplateTypeParmDecl>(i)) {
					if (tpd->getDepth() != depth)
						break;
					if (tpd->getIndex() == index) {
						guard::ctor _{print, "Tparam", false};
						return print.str(tpd->getName());
					}
				}
			}
		} else if (auto fd = dyn_cast<FunctionDecl>(d)) {
			if (auto y = fd->getTemplateSpecializationArgs()) {
				auto ary = y->asArray();
				always_assert(index < ary.size());
				return printQualType(print, ary[index].getAsType(), loc);

			} else if (auto x = fd->getDescribedTemplateParams())
				for (auto i : x->asArray()) {
					if (auto tpd = dyn_cast<TemplateTypeParmDecl>(i)) {
						if (tpd->getDepth() != depth)
							break;
						if (tpd->getIndex() == index) {
							always_assert(print.templates());
							guard::ctor _{print, "Tparam", false};
							return print.str(tpd->getName());
						}
					}
				}
		} else if (auto rd = dyn_cast<CXXRecordDecl>(d)) {
			if (auto x = rd->getDescribedTemplateParams())
				for (auto i : x->asArray()) {
					if (auto tpd = dyn_cast<TemplateTypeParmDecl>(i)) {
						if (tpd->getDepth() != depth)
							break;
						if (tpd->getIndex() == index) {
							always_assert(print.templates());
							guard::ctor _{print, "Tparam", false};
							return print.str(tpd->getName());
						}
					}
				}
		}
	}

	error_prefix(logging::debug(), loc)
		<< "error: could not infer template parameter name at depth " << depth
		<< ", index " << index << "\n";
	debug_dump(loc);
	logging::die();
}

fmt::Formatter &
ClangPrinter::printField(CoqPrinter &print, const ValueDecl *decl) {
	if (trace(Trace::Decl))
		trace("printField", loc::of(decl));

	return printName(print, *decl);
}

std::string
ClangPrinter::sourceLocation(const SourceLocation loc) const {
	return loc.printToString(this->context_->getSourceManager());
}

std::string
ClangPrinter::sourceRange(const SourceRange sr) const {
	return sr.printToString(this->context_->getSourceManager());
}

const Decl *
ClangPrinter::getDecl() const {
	return decl_ ? Decl::castFromDeclContext(decl_) : nullptr;
}

llvm::raw_ostream &
ClangPrinter::debug_dump(loc::loc loc) {
	return logging::debug() << loc::dump(loc, getContext(), getDecl());
}

llvm::raw_ostream &
ClangPrinter::error_prefix(llvm::raw_ostream &os, loc::loc loc) {
	return os << loc::prefix(loc, getContext(), getDecl());
}

llvm::raw_ostream &
ClangPrinter::trace(StringRef whence, loc::loc loc) {
	auto &os = llvm::errs();
	os << "[TRACE] " << whence;
	auto decl = getDecl();
	if (loc::can_trace(loc, decl))
		os << " " << loc::trace(loc, getContext(), decl);
	return os << "\n";
}

fmt::Formatter &
ClangPrinter::printVariadic(CoqPrinter &print, bool va) const {
	return print.output() << (va ? "Ar_Variadic" : "Ar_Definite");
}

fmt::Formatter &
ClangPrinter::printCallingConv(CoqPrinter &print, clang::CallingConv cc,
							   loc::loc loc) {
#define PRINT(x)                                                               \
	case CallingConv::x:                                                       \
		print.output() << #x;                                                  \
		break;
#define OVERRIDE(x, y)                                                         \
	case CallingConv::x:                                                       \
		print.output() << #y;                                                  \
		break;
	switch (cc) {
		PRINT(CC_C);
		OVERRIDE(CC_X86RegCall, CC_RegCall);
		OVERRIDE(CC_Win64, CC_MsAbi);
#if 0
	PRINT(CC_X86StdCall);
	PRINT(CC_X86FastCall);
	PRINT(CC_X86ThisCall);
	PRINT(CC_X86VectorCall);
	PRINT(CC_X86Pascal);
	PRINT(CC_X86_64SysV);
	PRINT(CC_AAPCS);
	PRINT(CC_AAPCS_VFP);
	PRINT(CC_IntelOclBicc);
	PRINT(CC_SpirFunction);
	PRINT(CC_OpenCLKernel);
	PRINT(CC_Swift);
	PRINT(CC_PreserveMost);
	PRINT(CC_PreserveAll);
	PRINT(CC_AArch64VectorCall);
#endif
	default:
		error_prefix(logging::fatal(), loc)
			<< "error: unsupported calling convention\n";
		debug_dump(loc);
		logging::die();
	}
	return print.output();
}
