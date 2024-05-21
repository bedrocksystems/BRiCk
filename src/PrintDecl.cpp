/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "Template.hpp"
#include "config.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/RecordLayout.h"
#include "clang/Basic/Builtins.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include <clang/AST/Type.h>
#include <clang/Basic/Version.inc>

using namespace clang;

const char *templateArgumentKindName(TemplateArgument::ArgKind);

[[noreturn]] static void
fatal(ClangPrinter &cprint, loc::loc loc, StringRef msg) {
	cprint.error_prefix(logging::fatal(), loc) << "error: " << msg << "\n";
	cprint.debug_dump(loc);
	logging::die();
}

static raw_ostream &
unsupported(ClangPrinter &cprint, loc::loc loc, const Twine &msg) {
	auto &os = cprint.error_prefix(logging::unsupported(), loc)
			   << "warning: unsupported " << msg << "\n";
	cprint.debug_dump(loc);
	return os;
}

static CallingConv
getCallingConv(const Type *type, ClangPrinter &cprint, loc::loc loc) {
	if (auto ft = dyn_cast_or_null<FunctionType>(type)) {
		return ft->getCallConv();
	} else if (auto at = dyn_cast_or_null<AttributedType>(type)) {
		return getCallingConv(at->getModifiedType().getTypePtr(), cprint, loc);
	} else if (auto toe = dyn_cast_or_null<TypeOfExprType>(type)) {
		return getCallingConv(toe->desugar().getTypePtr(), cprint, loc);
	} else
		fatal(cprint, loc,
			  "getCallingConv: FunctionDecl type is not a FunctionType");
}

fmt::Formatter &
ClangPrinter::printCallingConv(const FunctionDecl &decl, CoqPrinter &print) {
	if (ClangPrinter::debug && trace(Trace::Decl))
		trace("printCallingConv", loc::of(decl));
	auto loc = loc::of(decl);
	auto cc = getCallingConv(decl.getType().getTypePtr(), *this, loc);
	return printCallingConv(cc, print, loc);
}

// Template specializations
namespace {

/**
Decide if `decl` is an implicit C++ special member function.

These can show up in specialized structures but do not arise in
templated structures (where it is generally impossible to decide if a
given structure should have a given implicit).
*/
static bool
isImplicitSpecialMethod(const Decl &decl) {
	if (!decl.isImplicit())
		return false;
	// Order matters: constructors and destructors are methods.
	if (auto d = dyn_cast<CXXConstructorDecl>(&decl))
		return d->isDefaultConstructor() || d->isCopyConstructor() ||
			   d->isMoveConstructor();
	if (isa<CXXDestructorDecl>(&decl))
		return true;
	if (auto d = dyn_cast<CXXMethodDecl>(&decl))
		return d->isCopyAssignmentOperator() || d->isMoveAssignmentOperator();
	return false;
}

/// Decide if `decl` arose from template specialization
static bool
isSpecialized(const Decl &decl) {
	if (isImplicitSpecialMethod(decl))
		return false;
	if (auto d = dyn_cast<EnumConstantDecl>(&decl))
		return false; // avoid too many warnings

	// We conservatively avoid recoverPattern. Instead, we check the
	// declaration and its context for specializations.

	if (recoverSpecialization(decl))
		return true;
	for (auto ctx = decl.getDeclContext(); ctx; ctx = ctx->getParent()) {
		if (recoverSpecialization(*cast<Decl>(ctx)))
			return true;
	}
	return false;
}

/// Decide if `decl` is a template, or lives in a template scope
static bool
isTemplate(const Decl &decl) {
	if (recoverTemplate(decl))
		return true;
	for (auto ctx = decl.getDeclContext(); ctx; ctx = ctx->getParent()) {
		if (recoverTemplate(*cast<Decl>(ctx)))
			return true;
	}
	return false;
}
} // Template specializations

const NamedDecl *
recoverPattern(const Decl &decl) {
	// Declarations synthesized by template specialization include
	// pointers back to the "patterns" they specialize.
	if (auto d = dyn_cast<CXXRecordDecl>(&decl)) {
		if (auto pat = d->getInstantiatedFromMemberClass())
			return pat;
		return d->getTemplateInstantiationPattern();
	} else if (auto d = dyn_cast<FunctionDecl>(&decl)) {
		if (auto pat = d->getInstantiatedFromMemberFunction())
			return pat;
		if (auto pat = d->getInstantiatedFromDecl())
			return pat;
		return d->getTemplateInstantiationPattern();
	} else if (auto d = dyn_cast<EnumDecl>(&decl)) {
		if (auto pat = d->getInstantiatedFromMemberEnum())
			return pat;
		return d->getTemplateInstantiationPattern();
	} else if (auto d = dyn_cast<VarDecl>(&decl)) {
		if (auto pat = d->getInstantiatedFromStaticDataMember())
			return pat;
		return d->getTemplateInstantiationPattern();
	} else
		return nullptr;
}

[[nodiscard]] static bool
printSpecialization(const Decl &decl, CoqPrinter &print, ClangPrinter &cprint) {
	if (!print.templates() || !isSpecialized(decl))
		return false;

	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printSpecialization", loc::of(decl));

	if (auto pat = recoverPattern(decl)) {
		guard::ctor _(print, "Dinstantiation");
		cprint.printNameComment(decl, print) << fmt::nbsp;
		cprint.printMangledName(decl, print) << fmt::nbsp;
		cprint.printNameComment(*pat, print) << fmt::nbsp;
		cprint.printMangledName(*pat, print) << fmt::nbsp;
		cprint.printTemplateArguments(decl, print);
		return true;
	} else {
		unsupported(cprint, loc::of(decl), "template specialization");
		return false;
	}
}

/// Print an untemplated declaration
template<typename T>
using Printer = fmt::Formatter &(*)(const T &, CoqPrinter &, ClangPrinter &,
									const ASTContext &);

template<typename T>
struct DeclPrinter {

	const StringRef ctor;
	const Printer<T> print_body;
	const bool ast2_only;

	DeclPrinter() = delete;
	DeclPrinter(StringRef c, Printer<T> p, bool b = false)
		: ctor{c}, print_body{p}, ast2_only{b} {
		assert(p != nullptr);
	}

	/// Project a decl D from an inhabitant of T
	template<typename D>
	using ToDecl = const D &(*)(const T &);

	template<typename D>
	static inline const D &toDeclDecl(const D &decl) {
		return decl;
	}

	/// Set context using ClangPrinter::withDecl and emit
	///
	/// - `(ctor name body)` if `decl` is neither a template nor a
	/// specialization,
	///
	/// - `(ctor params name body)` (and, AST2 only, `(Dname name
	/// structured_name)`) if `decl` is a template, and
	///
	/// - `(Dinstantiation ..)` if `decl` is a specialization.

	template<typename D = T, ToDecl<D> unbox = toDeclDecl>
	[[nodiscard]] bool print(const T &box, CoqPrinter &print,
							 ClangPrinter &cprint,
							 const ASTContext &ctxt) const {
		const D &decl = unbox(box);
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("DeclPrinter::print", loc::of(decl));
		auto printDecl = [&](ClangPrinter &cprint) {
			if (print.templates()) {
				// We print untemplated code and template specializations
				// elsewhere.
				if (!decl.isTemplated() || isSpecialized(decl))
					return false;

				if (ast2_only && !print.ast2())
					return false;

				std::string ctor_template{ctor};
				if (!print.ast2())
					ctor_template += "_template";

				guard::ctor _(print, ctor_template);
				cprint.printNameComment(decl, print) << fmt::nbsp;
				cprint.printTemplateParameters(decl, print) << fmt::nbsp;
				cprint.printMangledName(decl, print) << fmt::nbsp;
				print_body(box, print, cprint, ctxt);
				return true;
			} else {
				guard::ctor _(print, ctor);
				cprint.printNameComment(decl, print) << fmt::nbsp;
				cprint.printMangledName(decl, print) << fmt::nbsp;
				print_body(box, print, cprint, ctxt);
				return true;
			}
		};
		auto printDeclWith = [&]() {
			if (auto declctx = dyn_cast<DeclContext>(&decl)) {
				auto cp = cprint.withDecl(declctx);
				return printDecl(cp);
			} else
				return printDecl(cprint);
		};
		auto printDeclWithName = [&]() {
			auto r = printDeclWith();
			if (r && print.templates() && print.ast2()) {
				/*
                This abstraction violation (presupposing we're printing
                a list of declarations) seems simpler than, say,
                changing the return type of ClangPrinter::printDecl to
                distinguish three cases. It's short term, as is `Dname`.
                */
				print.cons();

				guard::ctor _(print, "Dname");
				cprint.printNameComment(decl, print) << fmt::nbsp;
				cprint.printMangledName(decl, print) << fmt::nbsp;
				cprint.printStructuredName(decl, print);
			}
			return r;
		};
		return printDeclWithName() || printSpecialization(decl, print, cprint);
	}
};
template<typename D>
DeclPrinter(StringRef, Printer<D>, bool) -> DeclPrinter<D>;

// Incomplete types
namespace {
static fmt::Formatter &
printType(const TypeDecl &decl, CoqPrinter &print, ClangPrinter &cprint,
		  const ASTContext &ctxt) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printType", loc::of(decl));
	return print.output();
}
}
static const DeclPrinter Dtype("Dtype", printType, /*ast2_only*/ true);

// Type aliases
namespace {
static fmt::Formatter &
printTypedef(const TypedefNameDecl &decl, CoqPrinter &print,
			 ClangPrinter &cprint, const ASTContext &ctxt) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printTypedef", loc::of(decl));
	return cprint.printQualType(decl.getUnderlyingType(), print, loc::of(decl));
}
}
static const DeclPrinter Dtypedef("Dtypedef", printTypedef, /*ast2_only*/ true);

// Structures and unions
namespace {

static fmt::Formatter &
printClassName(const RecordDecl &decl, CoqPrinter &print,
			   ClangPrinter &cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printClassName", loc::of(decl));

	if (print.templates()) {
		/*
        NOTE (AST2): Locally, we know `decl` is a template, making it
        reasonable to synthesize _all_ template arguments from
        parameters. Nevertheless, we leave it to the type printer (and
        VisitInjectedClassNameType) to handle argument synthesis because
        such types get printed from other contexts.
        */
		return cprint.printType(decl.getTypeForDecl(), print, loc::of(decl));
	} else
		return cprint.printTypeName(decl, print);
}

static fmt::Formatter &
printClassName(const RecordDecl *decl, CoqPrinter &print, ClangPrinter &cprint,
			   loc::loc loc) {
	if (decl)
		return printClassName(*decl, print, cprint);
	else
		fatal(cprint, loc, "null class name");
}

static fmt::Formatter &
printClassName(const Type &type, CoqPrinter &print, ClangPrinter &cprint,
			   loc::loc loc) {
	if (auto decl = type.getAsCXXRecordDecl())
		return printClassName(*decl, print, cprint);
	else
		fatal(cprint, loc, "class name type not a record type");
}

static fmt::Formatter &
printClassName(const Type *type, CoqPrinter &print, ClangPrinter &cprint,
			   loc::loc loc) {
	if (type)
		return printClassName(*type, print, cprint, loc);
	else
		fatal(cprint, loc, "null class name type");
}
static fmt::Formatter &
printClassName(QualType type, CoqPrinter &print, ClangPrinter &cprint,
			   loc::loc loc) {
	return printClassName(type.getTypePtrOrNull(), print, cprint, loc);
}

static fmt::Formatter &
printLayoutInfo(CharUnits::QuantityType li, CoqPrinter &print) {
	guard::ctor _(print, "Build_LayoutInfo");
	return print.output() << li;
}

static const CXXRecordDecl *
getTypeAsRecord(const ValueDecl &decl) {
	if (auto type = decl.getType().getTypePtrOrNull())
		return type->getAsCXXRecordDecl();
	else
		return nullptr;
}

static fmt::Formatter &
printAnonymousFieldName(const FieldDecl &field, CoqPrinter &print,
						ClangPrinter &cprint) {
	/*
    TODO: We could support more unnamed fields using something like
    `mem_name : ident + N`.
    */
	auto unsupported = [&](StringRef msg) -> auto & {
		::unsupported(cprint, loc::of(field), msg);
		return cprint.printUnsupportedName(msg, print);
	};
	if (!print.ast2()) {
		guard::ctor _(print, "Nanon");
		if (auto rec = getTypeAsRecord(field))
			return cprint.printTypeName(rec, print, loc::of(field));
		else
			return unsupported("field not of record type");
	} else
		return unsupported("unnamed field");
}
}
fmt::Formatter &
ClangPrinter::printFieldName(const FieldDecl &field, CoqPrinter &print,
							 loc::loc) {
	if (auto id = field.getIdentifier())
		return print.str(id->getName());
	else
		return printAnonymousFieldName(field, print, *this);
}
namespace {
static fmt::Formatter &
printFieldInitializer(const FieldDecl &field, CoqPrinter &print,
					  ClangPrinter &cprint) {
	if (auto expr = field.getInClassInitializer()) {
		guard::some _(print);
		return cprint.printExpr(expr, print);
	} else
		return print.none();
}

static fmt::Formatter &
printFields(const CXXRecordDecl &decl, const ASTRecordLayout *layout,
			CoqPrinter &print, ClangPrinter &cprint) {
	auto i = 0;
	return print.list(decl.fields(), [&](auto field) {
		if (!field)
			fatal(cprint, loc::of(decl), "null field");
		if (field->isBitField())
			fatal(cprint, loc::of(field), "bit fields are not supported");

		guard::ctor _(print, "mkMember", i != 0);
		cprint.printFieldName(*field, print, loc::of(field)) << fmt::nbsp;
		cprint.printQualType(field->getType(), print, loc::of(field))
			<< fmt::nbsp;
		print.boolean(field->isMutable()) << fmt::nbsp;
		printFieldInitializer(*field, print, cprint) << fmt::nbsp;
		auto li = layout ? layout->getFieldOffset(i++) : 0;
		printLayoutInfo(li, print);
	});
}

static fmt::Formatter &
printStructBases(const CXXRecordDecl &decl, const ASTRecordLayout *layout,
				 CoqPrinter &print, ClangPrinter &cprint) {
	return print.list(decl.bases(), [&](CXXBaseSpecifier base) {
		auto fatal = [&](StringRef msg) NORETURN {
			auto loc = loc::refine(loc::of(decl), base.getTypeSourceInfo());
			::fatal(cprint, loc, msg);
		};

		if (base.isVirtual())
			fatal("virtual base classes are not supported");

		auto type = base.getType().getTypePtrOrNull();
		if (!type)
			fatal("null base class");

		auto dependent = [&]() -> auto & {
			guard::tuple _(print);
			cprint.printType(type, print, loc::of(decl)) << fmt::tuple_sep;
			return printLayoutInfo(0, print);
		};
		if (print.templates())
			return dependent();
		else if (auto record = type->getAsCXXRecordDecl()) {
			guard::tuple _(print);
			cprint.printTypeName(record, print, loc::of(type))
				<< fmt::tuple_sep;
			auto li =
				layout ? layout->getBaseClassOffset(record).getQuantity() : 0;
			return printLayoutInfo(li, print);
		} else if (!ClangPrinter::warn_well_known && type->isDependentType()) {
			/*
            The guard on `record` used to be an assert, and ignored.
            */
			return dependent();
		} else
			fatal("base class not of RecordType");
	});
}

bool
is_pure_virtual(const clang::FunctionDecl &d) {
#if 18 <= CLANG_VERSION_MAJOR
	return d.isPureVirtual();
#else
	return d.isPure();
#endif
}

static fmt::Formatter &
printStructVirtuals(const CXXRecordDecl &decl, CoqPrinter &print,
					ClangPrinter &cprint) {
	return print.list_filter(decl.methods(), [&](auto m) {
		if (!m)
			fatal(cprint, loc::of(decl), "null method");
		if (not m->isVirtual())
			return false;
		guard::ctor _(print, is_pure_virtual(*m) ? "pure_virt" : "impl_virt",
					  false);
		cprint.printObjName(m, print, loc::of(decl));
		return true;
	});
}

static fmt::Formatter &
printStructOverrides(const CXXRecordDecl &decl, CoqPrinter &print,
					 ClangPrinter &cprint) {
	guard::list _(print);
	for (auto m : decl.methods()) {
		if (!m)
			fatal(cprint, loc::of(decl), "null method");
		if (m->isVirtual() and not is_pure_virtual(*m)) {
			for (auto o : m->overridden_methods()) {
				print.output() << "(";
				cprint.printObjName(o, print, loc::of(m)) << fmt::tuple_sep;
				cprint.printObjName(*m, print) << ")" << fmt::cons;
			}
		}
	}
	return print.output();
}

static fmt::Formatter &
printDeleteName(const CXXRecordDecl &decl, CoqPrinter &print,
				ClangPrinter &cprint) {
	auto dtor = decl.getDestructor();
	auto del = dtor ? dtor->getOperatorDelete() : nullptr;
	if (del) {
		guard::some _(print);
		return cprint.printObjName(*del, print);
	} else
		return print.none();
}

static fmt::Formatter &
printTriviallyDestructible(const CXXRecordDecl &decl, CoqPrinter &print,
						   ClangPrinter &cprint) {
	return print.output() << fmt::BOOL(decl.hasTrivialDestructor());
}

static fmt::Formatter &
printLayoutType(const CXXRecordDecl &decl, CoqPrinter &print,
				ClangPrinter &cprint) {
	if (decl.isPOD()) {
		print.output() << "POD";
	} else if (decl.isStandardLayout()) {
		print.output() << "Standard";
	} else {
		print.output() << "Unspecified";
	}
	return print.output();
}

static fmt::Formatter &
printSizeAlign(const CXXRecordDecl &decl, const ASTRecordLayout *layout,
			   CoqPrinter &print, ClangPrinter &cprint) {
	auto size = layout ? layout->getSize().getQuantity() : 0;
	auto align = layout ? layout->getAlignment().getQuantity() : 0;
	return print.output() << size << fmt::nbsp << align;
}

static fmt::Formatter &
printStruct(const CXXRecordDecl &decl, CoqPrinter &print, ClangPrinter &cprint,
			const ASTContext &ctxt) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printStruct", loc::of(decl));
	assert(decl.getTagKind() == TagTypeKind::TTK_Class ||
		   decl.getTagKind() == TagTypeKind::TTK_Struct);

	if (!decl.isCompleteDefinition())
		return print.none();

	const auto layout =
		decl.isDependentContext() ? nullptr : &ctxt.getASTRecordLayout(&decl);

	guard::some some(print);
	guard::ctor _(print, "Build_Struct");

	printStructBases(decl, layout, print, cprint) << fmt::line;
	printFields(decl, layout, print, cprint) << fmt::nbsp;
	printStructVirtuals(decl, print, cprint) << fmt::nbsp;
	printStructOverrides(decl, print, cprint) << fmt::nbsp;
	cprint.printDtorName(decl, print) << fmt::nbsp;
	printTriviallyDestructible(decl, print, cprint) << fmt::nbsp;
	printDeleteName(decl, print, cprint) << fmt::line;
	printLayoutType(decl, print, cprint) << fmt::nbsp;
	return printSizeAlign(decl, layout, print, cprint);
}

static fmt::Formatter &
printUnion(const CXXRecordDecl &decl, CoqPrinter &print, ClangPrinter &cprint,
		   const ASTContext &ctxt) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printUnion", loc::of(decl));
	assert(decl.getTagKind() == TagTypeKind::TTK_Union);

	if (!decl.isCompleteDefinition())
		return print.none();

	const auto layout =
		decl.isDependentContext() ? nullptr : &ctxt.getASTRecordLayout(&decl);

	guard::some some(print);
	guard::ctor _(print, "Build_Union");

	printFields(decl, layout, print, cprint) << fmt::nbsp;
	cprint.printDtorName(decl, print) << fmt::nbsp;
	printTriviallyDestructible(decl, print, cprint) << fmt::nbsp;
	printDeleteName(decl, print, cprint) << fmt::line;
	return printSizeAlign(decl, layout, print, cprint);
}
} // structures and unions

static const DeclPrinter Dstruct("Dstruct", printStruct);
static const DeclPrinter Dunion("Dunion", printUnion);

// Functions
namespace {
static fmt::Formatter &
printBuiltin(Builtin::ID id, const ValueDecl &decl, CoqPrinter &print,
			 ClangPrinter &cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printBuiltin", loc::of(decl));
	switch (id) {
#define CASEB(x)                                                               \
	case Builtin::BI__builtin_##x:                                             \
		return print.output() << "Bin_" #x;
		CASEB(alloca)
		CASEB(alloca_with_align)
		CASEB(launder)
		// control flow
		CASEB(expect)
		CASEB(unreachable)
		CASEB(trap)
		// bitwise operations
		CASEB(bswap16)
		CASEB(bswap32)
		CASEB(bswap64)
		CASEB(ffs)
		CASEB(ffsl)
		CASEB(ffsll)
		CASEB(clz)
		CASEB(clzl)
		CASEB(clzll)
		CASEB(ctz)
		CASEB(ctzl)
		CASEB(ctzll)
		CASEB(popcount)
		CASEB(popcountl)
		// memory operations
		CASEB(memset)
		CASEB(memcmp)
		CASEB(bzero)
#undef CASEB
	default: {
		if (ClangPrinter::warn_well_known)
			unsupported(cprint, loc::of(decl), "builtin function");
		guard::ctor _(print, "Bin_unknown");
		return print.str(decl.getNameAsString());
	}
	}
}

static inline Builtin::ID
getBuiltin(const FunctionDecl &decl) {
	auto id = decl.getBuiltinID();
	if (Builtin::ID::NotBuiltin != id)
		return Builtin::ID(id);
	return Builtin::ID::NotBuiltin;
}

static fmt::Formatter &
printFunctionParams(const FunctionDecl &decl, CoqPrinter &print,
					ClangPrinter &cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printFunctionParams", loc::of(decl));
	auto loc = loc::of(decl);
	return print.list(decl.parameters(), [&](auto *param) {
		guard::tuple _(print);
		cprint.printParamName(param, print) << fmt::tuple_sep;
		cprint.printQualType(param->getType(), print, loc);
	});
}

static fmt::Formatter &
printFunction(const FunctionDecl &decl, CoqPrinter &print, ClangPrinter &cprint,
			  const ASTContext &) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printFunction", loc::of(decl));
	guard::ctor _(print, "Build_Func");
	cprint.printQualType(decl.getReturnType(), print, loc::of(decl))
		<< fmt::line;
	printFunctionParams(decl, print, cprint) << fmt::nbsp;
	cprint.printCallingConv(decl, print) << fmt::nbsp;
	cprint.printVariadic(decl.isVariadic(), print) << fmt::line;
	if (auto body = decl.getBody()) {
		guard::some some(print, false);
		guard::ctor _(print, "Impl", false);
		return cprint.printStmt(body, print);
	} else if (auto builtin = getBuiltin(decl)) {
		guard::some some(print, false);
		guard::ctor _(print, "Builtin", false);
		return printBuiltin(builtin, decl, print, cprint);
	} else {
		return print.none();
	}
}

static fmt::Formatter &
printMethod(const CXXMethodDecl &decl, CoqPrinter &print, ClangPrinter &cprint,
			const ASTContext &) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printMethod", loc::of(decl));

	print.output() << fmt::BOOL(decl.isStatic()) << fmt::nbsp;

	guard::ctor _(print, "Build_Method");
	cprint.printQualType(decl.getReturnType(), print, loc::of(decl))
		<< fmt::nbsp;
	printClassName(decl.getParent(), print, cprint, loc::of(decl)) << fmt::nbsp;
	cprint.printQualifier(decl.isConst(), decl.isVolatile(), print)
		<< fmt::nbsp;
	printFunctionParams(decl, print, cprint) << fmt::nbsp;
	cprint.printCallingConv(decl, print) << fmt::nbsp;
	cprint.printVariadic(decl.isVariadic(), print) << fmt::line;
	if (auto body = decl.getBody()) {
		guard::some some(print);
		guard::ctor _(print, "UserDefined");
		return cprint.printStmt(body, print);
	} else if (decl.isDefaulted()) {
		return print.output() << "(Some Defaulted)";
	} else {
		return print.none();
	}
}

// NOTE: We make implicit initialization explicit, and we resepect
// initialization order.
static ref<IdentifierInfo>
printIndirectFieldChain(const CXXConstructorDecl &ctor,
						const IndirectFieldDecl &decl, CoqPrinter &print,
						ClangPrinter &cprint) {
	auto fatal = [&](StringRef msg)
					 NORETURN { ::fatal(cprint, loc::of(decl), msg); };
	guard::list _(print);
	for (auto nd : decl.chain()) {
		if (auto id = nd->getIdentifier())
			return ref{*id};
		else if (auto fd = dyn_cast<FieldDecl>(nd)) {
			guard::tuple _(print);
			cprint.printFieldName(*fd, print, loc::of(decl)) << fmt::tuple_sep;
			printClassName(fd->getType(), print, cprint, loc::of(decl));
		} else
			fatal("non-field in indirect field chain");
		print.cons();
	}
	fatal("no named field in indirect field chain");
}

static fmt::Formatter &
printInitPath(const CXXConstructorDecl &decl, const CXXCtorInitializer &init,
			  CoqPrinter &print, ClangPrinter &cprint) {
	auto fatal = [&](StringRef msg)
					 NORETURN { ::fatal(cprint, loc::of(decl), msg); };
	if (init.isMemberInitializer()) {
		auto fd = init.getMember();
		if (fd) {
			// this can print an invalid field name
			guard::ctor _(print, "InitField", false);
			return cprint.printFieldName(*fd, print, loc::of(decl));
		} else
			fatal("field initializer with null field");
	} else if (init.isBaseInitializer()) {
		guard::ctor _(print, "InitBase", false);
		return printClassName(init.getBaseClass(), print, cprint,
							  loc::of(decl));
	} else if (init.isIndirectMemberInitializer()) {
		auto fd = init.getIndirectMember();
		if (!fd)
			fatal("indirect field initializer without field");
		guard::ctor _(print, "InitIndirect", false);
		auto id = printIndirectFieldChain(decl, *fd, print, cprint);
		print.output() << fmt::nbsp;
		return cprint.printFieldName(*fd->getAnonField(), print, loc::of(decl));
	} else if (init.isDelegatingInitializer())
		return print.output() << "InitThis";
	else
		fatal("initializer path of unknown type");
}

static fmt::Formatter &
printInitType(const CXXConstructorDecl &decl, const CXXCtorInitializer &init,
			  CoqPrinter &print, ClangPrinter &cprint) {
	// TODO: Print Tunsupported and keep going under ast2.
	auto fatal = [&](StringRef msg)
					 NORETURN { ::fatal(cprint, loc::of(decl), msg); };
	auto use_type = [&](const Type &type) -> auto & {
		return cprint.printType(type, print);
	};
	auto use_qualtype = [&](const QualType qt) -> auto & {
		return cprint.printQualType(qt, print, loc::of(decl));
	};
	if (auto fd = init.getMember())
		return use_qualtype(fd->getType());
	else if (auto fd = init.getIndirectMember())
		return use_qualtype(fd->getType());
	else if (auto type = init.getBaseClass())
		return use_type(*type);
	else if (init.isDelegatingInitializer())
		return use_qualtype(decl.getThisType());
	else
		fatal("initializer not memeber, base class, or indirect");
}

static fmt::Formatter &
printInitializer(const CXXConstructorDecl &ctor, const CXXCtorInitializer &init,
				 CoqPrinter &print, ClangPrinter &cprint) {
	auto e = init.getInit();
	if (!e)
		fatal(cprint, loc::of(ctor), "initializer without expression");
	guard::ctor _(print, "Build_Initializer");
	printInitPath(ctor, init, print, cprint) << fmt::line;
	printInitType(ctor, init, print, cprint) << fmt::nbsp;
	return cprint.printExpr(e, print);
}

static fmt::Formatter &
printInitializerList(const CXXConstructorDecl &decl, CoqPrinter &print,
					 ClangPrinter &cprint) {
	// The order here is corrrect with respect to initalization order.
	return print.list(decl.inits(), [&](auto init) {
		if (init)
			printInitializer(decl, *init, print, cprint);
		else
			fatal(cprint, loc::of(decl), "null initializer");
	});
}

static fmt::Formatter &
printConstructor(const CXXConstructorDecl &decl, CoqPrinter &print,
				 ClangPrinter &cprint, const ASTContext &) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printConstructor", loc::of(decl));
	guard::ctor _(print, "Build_Ctor");
	printClassName(decl.getParent(), print, cprint, loc::of(decl)) << fmt::nbsp;
	printFunctionParams(decl, print, cprint) << fmt::nbsp;
	cprint.printCallingConv(decl, print) << fmt::nbsp;
	cprint.printVariadic(decl.isVariadic(), print) << fmt::nbsp;
	if (auto body = decl.getBody()) {
		guard::some s(print);
		guard::ctor ud(print, "UserDefined");
		guard::tuple _(print);
		printInitializerList(decl, print, cprint) << fmt::tuple_sep;
		return cprint.printStmt(body, print);
	} else {
		return print.none();
	}
}

static fmt::Formatter &
printDestructor(const CXXDestructorDecl &decl, CoqPrinter &print,
				ClangPrinter &cprint, const ASTContext &) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printDestructor", loc::of(decl));

	guard::ctor _(print, "Build_Dtor");
	printClassName(decl.getParent(), print, cprint, loc::of(decl)) << fmt::nbsp;
	cprint.printCallingConv(decl, print) << fmt::nbsp;
	if (auto body = decl.getBody()) {
		guard::some some(print);
		guard::ctor _(print, "UserDefined");
		return cprint.printStmt(body, print);
	} else if (decl.isDefaulted()) {
		return print.output() << "(Some Defaulted)";
	} else {
		return print.none();
	}
}
} // Functions

static const DeclPrinter Dfunction("Dfunction", printFunction);
static const DeclPrinter Dmethod("Dmethod", printMethod);
static const DeclPrinter Dconstructor("Dconstructor", printConstructor);
static const DeclPrinter Ddestructor("Ddestructor", printDestructor);

// Variables
namespace {
static fmt::Formatter &
printVar(const VarDecl &decl, CoqPrinter &print, ClangPrinter &cprint,
		 const ASTContext &) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printVar", loc::of(decl));

	// TODO handling of [constexpr] needs to be improved.
	cprint.printQualType(decl.getType(), print, loc::of(decl)) << fmt::nbsp;
	if (auto e = decl.getInit()) {
		guard::some _(print);
		return cprint.printExpr(e, print);
	} else
		return print.none();
}
}
static const DeclPrinter Dvariable("Dvariable", printVar, /*ast2_only*/ true);

// Enumerations
namespace {

static fmt::Formatter &
printEnum(const EnumDecl &decl, CoqPrinter &print, ClangPrinter &cprint,
		  const ASTContext &) {
	auto loc = loc::of(decl);
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printEnum", loc);

	cprint.printQualType(decl.getIntegerType(), print, loc::of(decl))
		<< fmt::nbsp;
	// TODO: Tidy up enumeration constants. We might emit their values
	// here as well, rather than as separate declarations.
	auto printConst = [&](EnumConstantDecl *c) {
		cprint.printUnqualifiedName(c, print, loc);
	};
	return print.list(decl.enumerators(), printConst);
}

/// Types that BRiCk represents using [Tchar_]
static bool
isBRiCkCharacterType(const BuiltinType &type) {
	switch (type.getKind()) {
	case BuiltinType::Kind::Char_S:
	case BuiltinType::Kind::Char_U:
	case BuiltinType::Kind::WChar_S:
	case BuiltinType::Kind::WChar_U:
	case BuiltinType::Kind::Char16:
	case BuiltinType::Kind::Char8:
	case BuiltinType::Kind::Char32:
		return true;
	default:
		return false;
	}
}

static uint64_t
toBRiCkCharacter(size_t bitsize, int64_t val) {
	return static_cast<uint64_t>(val) & ((1ull << bitsize) - 1);
}

struct EnumConst {
	struct UVal {
		// TODO: bool
		const enum Kind { Kint, Kchar } kind;
		const size_t bitsize;
		const llvm::APSInt val;
		UVal() = delete;
		UVal(llvm::APSInt v) : kind{Kint}, bitsize{0}, val{v} {}
		UVal(size_t sz, llvm::APSInt v) : kind{Kchar}, bitsize{sz}, val{v} {}

		fmt::Formatter &print(CoqPrinter &print) const {
			switch (kind) {
			case Kint: {
				return print.output() << "(inr " << val << ")";
			}
			case Kchar: {
				auto c = toBRiCkCharacter(bitsize, val.getExtValue());
				return print.output() << "(inl " << c << "%N)";
			}
			}
		}
	};

	const EnumConstantDecl &ec;
	const EnumDecl &ed;
	const QualType ut;
	const UVal uv;

	EnumConst() = delete;
	EnumConst(const EnumConstantDecl &c, const EnumDecl &e, const QualType u,
			  const UVal v)
		: ec{c}, ed{e}, ut{u}, uv{v} {}
};

static const EnumConstantDecl &
enumConstToDecl(const EnumConst &c) {
	return c.ec;
}

static std::optional<EnumConst>
crackEnumConst(const EnumConstantDecl &decl, CoqPrinter &print,
			   ClangPrinter &cprint, const ASTContext &ctxt) {
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("crackEnumConst", loc::of(decl));
	auto fail = [&](const Twine &msg) NODISCARD {
		unsupported(cprint, loc::of(decl),
					Twine("enumeration constant: ").concat(msg));
		return std::nullopt;
	};
	auto ed = dyn_cast_or_null<EnumDecl>(decl.getDeclContext());
	if (!ed)
		return fail("no enum");
	auto ut = ed->getIntegerType();
	if (ut.isNull())
		return fail("underlying type not integral");
	auto bt = ut.getTypePtr()->getAs<BuiltinType>();
	if (!bt) {
		/*
        TODO: With work here and in Coq, we might support constants in
        enumerations with dependent underlying types.
        */
		return fail("underlying integral type not a builtin");
	}
	if (isTemplate(*ed)) {
		/*
        TODO: With work here, we could print concrete enumeration
        constants in dependent scopes.
        */
		return fail("dependent scope");
	}

	auto ret = [&](auto uv) -> std::optional<EnumConst> {
		EnumConst c(decl, *ed, ut, uv);
		return {c};
	};
	auto v = decl.getInitVal();
	if (isBRiCkCharacterType(*bt))
		return ret(EnumConst::UVal(ctxt.getTypeSize(bt), v));
	else
		return ret(EnumConst::UVal(v));
}

static fmt::Formatter &
printEnumConst(const EnumConst &c, CoqPrinter &print, ClangPrinter &cprint,
			   const ASTContext &) {
	auto &[decl, ed, ut, uv] = c;
	if (ClangPrinter::debug && cprint.trace(Trace::Decl))
		cprint.trace("printEnumConst", loc::of(decl));

	cprint.printTypeName(ed, print) << fmt::nbsp;
	cprint.printQualType(ut, print, loc::of(decl)) << fmt::nbsp;
	uv.print(print) << fmt::nbsp;
	if (auto e = decl.getInitExpr()) {
		guard::some _(print);
		cprint.printExpr(e, print);
	} else
		print.none();
	return print.output();
}
} // Enumerations

static const DeclPrinter Denum("Denum", printEnum, /*ast2_only*/ true);
static const DeclPrinter Denum_constant("Denum_constant", printEnumConst,
										/*ast2_only*/ true);

// Static asserts
namespace {
static const StringLiteral *
staticAssertMessage(const StaticAssertDecl &decl) {
#if CLANG_VERSION_MAJOR <= 16
	return decl.getMessage();
#else
	return dyn_cast_or_null<StringLiteral>(decl.getMessage());
#endif
}
}

class PrintDecl :
	public ConstDeclVisitorArgs<PrintDecl, bool, CoqPrinter &, ClangPrinter &,
								const ASTContext &> {
private:
	PrintDecl() = default;

public:
	static PrintDecl printer;

	bool VisitDecl(const Decl *decl, CoqPrinter &print, ClangPrinter &cprint,
				   const ASTContext &) {
		unsupported(cprint, loc::of(decl), "declaration");
		return false;
	}

#define IGNORE(D)                                                              \
	bool Visit##D(const D *, CoqPrinter &, ClangPrinter &,                     \
				  const ASTContext &) {                                        \
		return false;                                                          \
	}

	IGNORE(EmptyDecl)
	IGNORE(FriendDecl)
	IGNORE(IndirectFieldDecl)
	IGNORE(LinkageSpecDecl)
	IGNORE(UsingDecl)
	IGNORE(UsingDirectiveDecl)
	IGNORE(UsingShadowDecl)

#undef IGNORE

	// Variables

	bool VisitVarDecl(const VarDecl *decl, CoqPrinter &print,
					  ClangPrinter &cprint, const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitVarDecl", loc::of(decl));

		return Dvariable.print(*decl, print, cprint, ctxt);
	}

	// Functions

	bool VisitFunctionDecl(const FunctionDecl *decl, CoqPrinter &print,
						   ClangPrinter &cprint, const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitFunctionDecl", loc::of(decl));
		return Dfunction.print(*decl, print, cprint, ctxt);
	}

	bool VisitCXXMethodDecl(const CXXMethodDecl *decl, CoqPrinter &print,
							ClangPrinter &cprint, const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitCXXMethodDecl", loc::of(decl));
		return Dmethod.print(*decl, print, cprint, ctxt);
	}

	bool VisitCXXConstructorDecl(const CXXConstructorDecl *decl,
								 CoqPrinter &print, ClangPrinter &cprint,
								 const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitCXXConstructorDecl", loc::of(decl));
		return Dconstructor.print(*decl, print, cprint, ctxt);
	}

	bool VisitCXXDestructorDecl(const CXXDestructorDecl *decl,
								CoqPrinter &print, ClangPrinter &cprint,
								const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitCXXDestructorDecl", loc::of(decl));
		return Ddestructor.print(*decl, print, cprint, ctxt);
	}

	// Type aliases

	bool VisitTypedefNameDecl(const TypedefNameDecl *decl, CoqPrinter &print,
							  ClangPrinter &cprint, const ASTContext &ctxt) {
		/*
        TODO: Adjust `type_table_le` and the template logic.
        */
		return false;

		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitTypedefNameDecl", loc::of(decl));

		auto go = [&]() { return Dtypedef.print(*decl, print, cprint, ctxt); };

		if (print.templates())
			return go();

		if (auto t = decl->getUnderlyingType().getTypePtrOrNull())
			if (!t->isDependentType())
				return go();

		if (ClangPrinter::warn_well_known)
			unsupported(cprint, loc::of(decl), "dependent typedef");
		return false;
	}

	// Types

	template<typename D>
	bool printType(const DeclPrinter<D> &printer, const D &decl,
				   CoqPrinter &print, ClangPrinter &cprint,
				   const ASTContext &ctxt) {
		if (decl.isCompleteDefinition())
			return printer.print(decl, print, cprint, ctxt);
		else
			return Dtype.print(decl, print, cprint, ctxt);
	}

	bool VisitUnionDecl(const CXXRecordDecl *decl, CoqPrinter &print,
						ClangPrinter &cprint, const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitUnionDecl", loc::of(decl));
		return printType(Dunion, *decl, print, cprint, ctxt);
	}

	bool VisitStructDecl(const CXXRecordDecl *decl, CoqPrinter &print,
						 ClangPrinter &cprint, const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitStructDecl", loc::of(decl));
		return printType(Dstruct, *decl, print, cprint, ctxt);
	}

	bool VisitCXXRecordDecl(const CXXRecordDecl *decl, CoqPrinter &print,
							ClangPrinter &cprint, const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitCXXRecordDecl", loc::of(decl));
		if (decl->isStruct() or decl->isClass()) {
			return VisitStructDecl(decl, print, cprint, ctxt);
		} else if (decl->isUnion()) {
			return VisitUnionDecl(decl, print, cprint, ctxt);
		} else {
			std::string msg;
			llvm::raw_string_ostream os{msg};
			os << "CXXRecord with tag kind " << decl->getKindName();
			unsupported(cprint, loc::of(decl), msg);
			return false;
		}
	}

	// Declarations that are only indirectly templated

	bool VisitEnumDecl(const EnumDecl *decl, CoqPrinter &print,
					   ClangPrinter &cprint, const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitEnumDecl", loc::of(decl));

		// The isCompleteDefinition in printType seems inadequate for
		// enumerations.
		if (decl->getIntegerType().isNull()) {
			if (!decl->getIdentifier()) {
				unsupported(cprint, loc::of(decl),
							"anonymous forward declaration");
				return false;
			} else
				return Dtype.print(*decl, print, cprint, ctxt);
		} else
			return Denum.print(*decl, print, cprint, ctxt);
	}

	bool VisitEnumConstantDecl(const EnumConstantDecl *decl, CoqPrinter &print,
							   ClangPrinter &cprint, const ASTContext &ctxt) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitEnumConstantDecl", loc::of(decl));
		if (auto c = crackEnumConst(*decl, print, cprint, ctxt))
			return Denum_constant.print<EnumConstantDecl, enumConstToDecl>(
				*c, print, cprint, ctxt);
		else
			return false;
	}

	bool VisitStaticAssertDecl(const StaticAssertDecl *decl, CoqPrinter &print,
							   ClangPrinter &cprint, const ASTContext &) {
		if (ClangPrinter::debug && cprint.trace(Trace::Decl))
			cprint.trace("VisitStaticAssertDecl", loc::of(decl));
		/*
        TODO: There _might_ be a case for supporting templated static
        asserts (e.g., when they have complicated proofs based mostly on
        templated code)).
        */
		if (auto e = decl->getAssertExpr()) {
			guard::ctor _(print, "Dstatic_assert");
			/*
            TODO: We insist on a StringLiteral message (the historical
            type). Consider dropping that requirement and using
            Stmt::printPretty.
            */
			if (auto msg = staticAssertMessage(*decl)) {
				guard::some _(print);
				print.str(msg->getString());
			} else {
				print.none();
			}
			print.output() << fmt::nbsp;
			cprint.printExpr(e, print);
			return true;
		} else {
			unsupported(cprint, loc::of(decl),
						"static assert without expression");
			return false;
		}
	}
};

PrintDecl PrintDecl::printer;

bool
ClangPrinter::printDecl(const clang::Decl *decl, CoqPrinter &print) {
	if (trace(Trace::Decl))
		trace("printDecl", loc::of(decl));
	return PrintDecl::printer.Visit(decl, print, *this, *context_);
}
