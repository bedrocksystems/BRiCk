/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "Template.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>
#include <clang/Basic/Version.inc>
#include <clang/Frontend/CompilerInstance.h>
#include <optional>

using namespace clang;

const TemplateDecl*
recoverTemplate(const Decl& decl) {
	if (auto td = dyn_cast<TemplateDecl>(&decl))
		return td;
	if (auto rd = dyn_cast<CXXRecordDecl>(&decl))
		return rd->getDescribedClassTemplate();
	if (auto fd = dyn_cast<FunctionDecl>(&decl))
		return fd->getDescribedFunctionTemplate();
	if (auto td = dyn_cast<TypeAliasDecl>(&decl))
		return td->getDescribedAliasTemplate();
	if (auto vd = dyn_cast<VarDecl>(&decl))
		return vd->getDescribedVarTemplate();
	return nullptr;
}

const char*
templateArgumentKindName(TemplateArgument::ArgKind kind) {
#define CASE(k)                                                                \
	case TemplateArgument::ArgKind::k:                                         \
		return #k;
	switch (kind) {
		CASE(Null)
		CASE(Type)
		CASE(Declaration)
		CASE(NullPtr)
		CASE(Integral)
		CASE(Template)
		CASE(TemplateExpansion)
		CASE(Expression)
		CASE(Pack)
	default:
		return "<unknown>";
	}
#undef CASE
}

namespace structured {

using ParameterLists =
	SmallVector<std::pair<const TemplateParameterList*, loc::loc>>;

// Returns the total length of lists appended to dest
static unsigned
collectParameterLists(const Decl& decl, const ASTContext& context,
					  ParameterLists& dest) {
	auto n = 0;
	if (auto ctx = decl.getDeclContext()) {
		auto loc = loc::of(decl);
		auto& cdecl = cast<const Decl>(*ctx);
		n += collectParameterLists(cdecl, context, dest);
		if (auto td = recoverTemplate(decl)) {
			if (auto params = td->getTemplateParameters()) {
				n += params->size();
				dest.push_back(std::make_pair(params, loc));
			} else {
				// TODO: Drop this function
				// and instead emit a marker
				// like `?null`.
				locfree_warn(decl, context,
							 "collectParameterLists "
							 "ignoring template with null "
							 "parameter list");
			}
		}
	}
	return n;
}

static raw_ostream&
printTemplateParameters(raw_ostream& os, const Decl& decl,
						const ASTContext& context) {
	ParameterLists lists;
	auto n = collectParameterLists(decl, context, lists);
	if (!lists.empty()) {
		auto& policy = context.getPrintingPolicy();
		os << '<';
		for (auto [params, loc] : lists) {
			for (auto param : params->asArray()) {
				param->printName(os, policy);
				if (--n)
					os << ", ";
			}
		}
		os << '>';
	}
	return os;
}

static raw_ostream&
printFunctionParameterTypes(raw_ostream& os, const FunctionDecl& decl,
							const PrintingPolicy& policy) {
	os << '(';
	auto ps = decl.parameters();
	for (size_t i = 0; i < ps.size(); i++) {
		if (auto vd = ps[i])
			vd->getType().print(os, policy);
		else
			os << "?null";
		if (i + 1 < ps.size())
			os << ", ";
	}
	os << ')';
	return os;
}

const FunctionDecl*
recoverFunction(const Decl& decl) {
	if (auto fd = dyn_cast<FunctionDecl>(&decl))
		return fd;
	if (auto td = dyn_cast<FunctionTemplateDecl>(&decl))
		return td->getTemplatedDecl();
	return nullptr;
}

static raw_ostream&
printFunctionQualifiersForDiagnostics(raw_ostream& os,
									  const FunctionDecl& decl) {
	if (auto md = dyn_cast<CXXMethodDecl>(&decl)) {
		if (md->isConst()) {
			os << " const";
		}
		if (md->isVolatile()) {
			os << " volatile";
		}
		switch (md->getRefQualifier()) {
		case RefQualifierKind::RQ_LValue:
			os << " &";
			break;
		case RefQualifierKind::RQ_RValue:
			os << " &&";
			break;
		default:
			break;
		}
	}
	return os;
}

raw_ostream&
printNameForDiagnostics(raw_ostream& os, const NamedDecl& decl,
						const ASTContext& context) {
	printTemplateParameters(os, decl, context);
	auto& policy = context.getPrintingPolicy();
	decl.getNameForDiagnostic(os, policy, true);
	// TODO: Make template arguments explicit in all cases?
	if (auto fd = recoverFunction(decl)) {
		printFunctionParameterTypes(os, *fd, policy);
		printFunctionQualifiersForDiagnostics(os, *fd);
	}
	return os;
}
} // namespace structured

static raw_ostream&
fatal(ClangPrinter& cprint, loc::loc loc) {
	cprint.debug_dump(loc);
	return cprint.error_prefix(logging::fatal(), loc) << "error: ";
}

static raw_ostream&
warning(ClangPrinter& cprint, loc::loc loc, bool dump = true) {
	if (dump)
		cprint.debug_dump(loc);
	return cprint.error_prefix(logging::unsupported(), loc) << "warning: ";
}

static raw_ostream&
unsupported(ClangPrinter& cprint, loc::loc loc, bool dump = true) {
	return warning(cprint, loc, dump) << "unsupported ";
}

static ref<const Decl>
toDecl(const DeclContext& ctx, ClangPrinter& cprint, loc::loc loc) {
	if (auto p = dyn_cast<Decl>(&ctx))
		return ref{*p};
	else {
		fatal(cprint, loc) << "declaration context of kind "
						   << ctx.getDeclKindName() << " not a declaration\n";
		logging::die();
	}
}

namespace mangled {

/*
This mangler is incomplete but handles a large
enough fragment of C++ to be useful in the short term.

NOTE: The existing ItaniumMangler does *almost* what we want
except it does not produce cross-translation unit unique names
for anonymous types which renders it largely unusable for
modular verification purposes.

TODO:
- Cover all declarations, not just named declarations

- Move away from Itanium mangling (which can crash on template
parameters and which does not cover enough names for verification
and which assigns disambiguating numbers different from those used
in `Nanon` and which does not lend itself to efficient demangling)
*/

static GlobalDecl
to_gd(const NamedDecl* decl) {
	if (auto ct = dyn_cast<CXXConstructorDecl>(decl)) {
		return GlobalDecl(ct, CXXCtorType::Ctor_Complete);
	} else if (auto dt = dyn_cast<CXXDestructorDecl>(decl)) {
		return GlobalDecl(dt, CXXDtorType::Dtor_Deleting);
	} else {
		return GlobalDecl(decl);
	}
}

static size_t
printSimpleContext(const DeclContext* dc, CoqPrinter& print,
				   ClangPrinter& cprint, size_t remaining = 0) {
	auto loc = loc::of(dc);
	auto unsupported = [&](StringRef what) {
		if (ClangPrinter::warn_well_known)
			::unsupported(cprint, loc) << what << "\n";
	};
	auto& mangle = cprint.getMangleContext();
	if (dc == nullptr or dc->isTranslationUnit()) {
		print.output() << "_Z" << (1 < remaining ? "N" : "");
		return 0;
	} else if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(dc)) {
		if (auto dtor = ts->getDestructor()) {
			// HACK: this mangles an aggregate name by mangling
			// the destructor and then doing some string manipulation
			std::string sout;
			llvm::raw_string_ostream out(sout);
			mangle.mangleName(to_gd(dtor), out);
			out.flush();
			always_assert(3 < sout.length() &&
						  "mangled string length is too small");
			sout =
				sout.substr(0, sout.length() - 4); // cut off the final 'DnEv'
			if (not ts->getDeclContext()->isTranslationUnit() or
				0 < remaining) {
				print.output() << sout << (remaining == 0 ? "E" : "");
				return 2; // we approximate the whole string by 2
			} else {
				print.output() << "_Z" << sout.substr(3, sout.length() - 3);
				return 1;
			}
		} else {
			unsupported("ClassTemplateSpecializationDecl for simple contexts");
			std::string sout;
			{
				llvm::raw_string_ostream out(sout);
#if 18 <= CLANG_VERSION_MAJOR
				mangle.mangleCanonicalTypeName(
					QualType(ts->getTypeForDecl(), 0), out);
#else
				mangle.mangleTypeName(QualType(ts->getTypeForDecl(), 0), out);
#endif
			}

			if (sout.substr(0, 4) == "_ZTS") {
				print.output() << "_Z" << sout.substr(4);
			} else {
				print.output() << sout;
			}
			return 2;
		}
	} else if (auto ns = dyn_cast<NamespaceDecl>(dc)) {
		auto parent = ns->getDeclContext();
		auto compound =
			printSimpleContext(parent, print, cprint, remaining + 1);
		if (not ns->isAnonymousNamespace()) {
			auto name = ns->getNameAsString();
			print.output() << name.length() << name;
		} else if (not ns->decls_empty()) {
			// a proposed scheme is to use the name of the first declaration.
			print.output() << "~<TODO>";
			// TODO
			// ns->field_begin()->printName(print.output().nobreak());
		} else {
			unsupported("empty anonymous namespace");
			print.output() << "~<empty>";
		}
		if (remaining == 0 && 0 < compound)
			print.output() << "E";
		return compound + 1;
	} else if (auto rd = dyn_cast<RecordDecl>(dc)) {
		// NOTE: this occurs when you have a forward declaration,
		// e.g. [struct C;], or when you have a compiler builtin.
		// We need to mangle the name, but we can't really get any help
		// from clang.

		auto parent = rd->getDeclContext();
		auto compound =
			printSimpleContext(parent, print, cprint, remaining + 1);
		if (rd->getIdentifier()) {
			auto name = rd->getNameAsString();
			print.output() << name.length() << name;
		} else if (auto tdn = rd->getTypedefNameForAnonDecl()) {
			auto s = tdn->getNameAsString();
			print.output() << s.length() << s;
			//tdn->printName(print.output().nobreak());
		} else if (not rd->field_empty()) {
			auto s = rd->field_begin()->getName();
			print.output() << s.size() + 1 << "."
						   << rd->field_begin()->getName();
		} else {
			// TODO this isn't technically sound
			unsupported("empty anonymous record");
			print.output() << "8~<empty>";
		}
		if (remaining == 0 && 0 < compound)
			print.output() << "E";
		return compound + 1;
	} else if (auto ed = dyn_cast<EnumDecl>(dc)) {
		auto parent = ed->getDeclContext();
		auto compound =
			printSimpleContext(parent, print, cprint, remaining + 1);
		if (ed->getIdentifier()) {
			auto name = ed->getNameAsString();
			print.output() << name.length() << name;
			//} else if (auto tdn = rd->getTypedefNameForAnonDecl()) {
			//    llvm::errs() << "typedef name not null " << tdn << "\n";
			//    tdn->printName(print.output().nobreak());
		} else {
			if (ed->enumerators().empty()) {
				// no idea what to do
				unsupported("unnamed, empty enumeration");
				print.output() << "13~<empty-enum>";
			} else {
				std::string out_s{};
				llvm::raw_string_ostream out{out_s};
				ed->enumerators().begin()->printName(out);
				out.flush();
				print.output() << out_s.size() + 1 << "~" << out_s;
			}
		}
		if (remaining == 0 && 0 < compound)
			print.output() << "E";
		return compound + 1;
	} else if (auto fd = dyn_cast<FunctionDecl>(dc)) {
		std::string sout;
		llvm::raw_string_ostream out(sout);
		mangle.mangleName(to_gd(fd), out);
		out.flush();
		always_assert(3 < sout.length() &&
					  "mangled string length is too small");
		if (not fd->getDeclContext()->isTranslationUnit()) {
			print.output() << sout << (remaining == 0 ? "E" : "");
			return 2; // we approximate the whole string by 2
		} else {
			print.output() << sout;
			return 1;
		}
	} else if (auto ls = dyn_cast<LinkageSpecDecl>(dc)) {
		auto parent = ls->getDeclContext();
		return printSimpleContext(parent, print, cprint, remaining);
	} else {
		fatal(cprint, loc)
			<< "unexpected declaration context in [printSimplContext]\n";
		logging::die();
	}
}

static fmt::Formatter&
printQualifiedName(const NamedDecl& decl, CoqPrinter& print,
				   ClangPrinter& cprint) {
	print.output() << '\"';
	auto& os = print.output().nobreak();
	decl.printQualifiedName(os);
	return print.output() << '\"';
}

static fmt::Formatter&
printTypeName(CoqPrinter& print, const TypeDecl& decl, ClangPrinter& cprint) {
	switch (decl.getKind()) {
	case Decl::Kind::CXXRecord:
	case Decl::Kind::ClassTemplateSpecialization:
	case Decl::Kind::Enum:
		print.output() << "\"";
		printSimpleContext(cast<DeclContext>(&decl), print, cprint);
		return print.output() << "\"";

	case Decl::Kind::Record:
		// NOTE: this only matches C records, not C++ records
		// therefore, we do not perform any mangling.
	case Decl::Kind::Typedef:
	case Decl::Kind::TypeAlias:
		return printQualifiedName(decl, print, cprint);

	default:
		if (ClangPrinter::warn_well_known)
			unsupported(cprint, loc::of(decl)) << "type in [printTypeName]\n";
		return print.str("~<unsupported-type>");
	}
}

// NOTE we implement our own destructor mangling because we are not
// guaranteed to be able to generate the destructor for every aggregate
// and our current setup requires that all aggregates have named
// destructors.
//
// An alternative (cleaner) solution is to extend the type of names to
// introduce a distinguished name for destructors. Doing this is a bit
// more invasive.
static fmt::Formatter&
printDtorName(CoqPrinter& print, const CXXRecordDecl& decl,
			  ClangPrinter& cprint) {
	guard::ctor _(print, "DTOR", false);
	return mangled::printTypeName(print, decl, cprint);
}

static fmt::Formatter&
printObjName(CoqPrinter& print, const ValueDecl& decl, ClangPrinter& cprint) {
	// All enumerations introduce types, but only some of them have names.
	// While positional names work in scoped contexts, they generally
	// do not work in extensible contexts (e.g. the global context)
	//
	// To address this, we use the name of their first declation.
	// To avoid potential clashes (since the first declaration might be
	// a term name and not a type name), we prefix the symbol with a dot,
	// e.g.
	// [enum { X , Y , Z };] -> [.X]
	// note that [MangleContext::mangleTypeName] does *not* follow this
	// strategy.

	auto& mangle = cprint.getMangleContext();
	if (auto ecd = dyn_cast<EnumConstantDecl>(&decl)) {
		// While they are values, they are not mangled because they do
		// not end up in the resulting binary. Therefore, we need a special
		// case.
		if (auto ed = dyn_cast<EnumDecl>(ecd->getDeclContext())) {
			guard::ctor _(print, "Nenum_const", false);
			printTypeName(print, *ed, cprint) << fmt::nbsp;
			return cprint.printUnqualifiedName(print, *ecd);
		} else {
			unsupported(cprint, loc::of(decl))
				<< "enumeration constant without declaration context\n";
			return print.output() << "~<bad enum constant>";
		}
	} else if (auto dd = dyn_cast<CXXDestructorDecl>(&decl)) {
		if (auto cls = dd->getParent()) {
			return printDtorName(print, *cls, cprint);
		} else {
			unsupported(cprint, loc::of(decl)) << "destructor without parent\n";
			return print.output() << "~<bad destructor>";
		}
	} else if (mangle.shouldMangleDeclName(&decl)) {
		print.output() << "\"";
		mangle.mangleName(to_gd(&decl), print.output().nobreak());
		return print.output() << "\"";
	} else {
		return cprint.printUnqualifiedName(print, decl);
	}
}

static fmt::Formatter&
printName(CoqPrinter& print, const Decl& decl, ClangPrinter& cprint) {
	if (isa<TypeDecl>(decl))
		return printTypeName(print, cast<TypeDecl>(decl), cprint);
	else if (isa<ValueDecl>(decl))
		return printObjName(print, cast<ValueDecl>(decl), cprint);
	else {
		unsupported(cprint, loc::of(decl)) << "cannot mangle declarations\n";
		return print.output() << "~<bad named declaration>";
	}
}

} // namespace mangled

namespace structured {

/*
We classify declaration contexts into

- _global_ contexts (translation units, implicit in `Nglobal`)
- _scope_ contexts (these show up under `Nscoped`)
- _ignorable_ contexts (these are suppressed in `Nscoped`)

We assign anonymous indices to any declaration `D` inherting from `Decl`
but not `NamedDecl`, as well as to a few ostensibly named declarations
which lack a name (e.g., unnamed, unscoped enumerations).

To assign an anonymous index to a declaration, we count relative to its
first non-ignorable ancestor. Such an ancestor always exists because the
declarations we name arise in the context of a translation unit, which
isn't ignorable. (It would be a mistake to, for example, suppress
ignorable contexts in `Nscoped` but then to number an anonymous
declaration relative to its ignored-by-`Nscoped` parent.)

We permit more anonymous declarations than the Itanium ABI because we
are not free to ignore names with internal linkage (which matter for
verification). Fortunately, we don't need our anonymous indices to match
the numbers picked by the ABI (e.g., in its  nonterminals
<<discriminator>>, <<unnamed-type-name>>).

TODO: Clang does not use declaration contexts to separate names with
internal linkage inside function bodies. To assign disambiguating
anonymous indices, we have to traverse the function's body, and not just
the declaration context chain. See FunctionDecl::getBody and
Stmt::children.
*/

enum class ContextKind { Global, Scope, Ingorable };

static ContextKind
classifyContext(const DeclContext& ctx, ClangPrinter& cprint) {
	if (false && cprint.trace(Trace::Name))
		cprint.trace("classifyContext", loc::of(ctx));

	switch (ctx.getDeclKind()) {
	case Decl::Kind::TranslationUnit:
		return ContextKind::Global;

	case Decl::Kind::Namespace:
	case Decl::Kind::Record:
	case Decl::Kind::CXXRecord:
	case Decl::Kind::ClassTemplateSpecialization:
	case Decl::Kind::ClassTemplatePartialSpecialization:
	case Decl::Kind::Function:
	case Decl::Kind::CXXMethod:
	case Decl::Kind::CXXConstructor:
	case Decl::Kind::CXXDestructor:
	case Decl::Kind::CXXConversion:
	case Decl::Kind::Block:
		return ContextKind::Scope;

	case Decl::Kind::Enum:
		/*
		technically, un-scoped enumerations are ignorable, but, for uniformity,
		   we always use qualifiers on enumeration constants.
		return cast<EnumDecl>(ctx).isScoped() ? ContextKind::Scope :
												ContextKind::Ingorable;
		*/
		return ContextKind::Scope;

	case Decl::Kind::LinkageSpec:
	case Decl::Kind::ExternCContext:
	case Decl::Kind::Export:
	case Decl::Kind::RequiresExprBody:
	case Decl::Kind::CXXDeductionGuide:
		return ContextKind::Ingorable;

	default: {
		warning(cprint, loc::of(ctx)) << "ignoring declaration context\n";
		return ContextKind::Ingorable;
	}
	}
}

static bool
isIgnorableContext(const DeclContext& ctx, ClangPrinter& cprint) {
	return classifyContext(ctx, cprint) == ContextKind::Ingorable;
}

static ref<const DeclContext>
getNonIgnorableAncestor(const Decl& decl, ClangPrinter& cprint) {
	auto fatal = [&](const std::string what, loc::loc loc) NORETURN {
		::fatal(cprint, loc) << what << "\n";
		logging::die();
	};
	auto parent = [&](const DeclContext* ctx) {
		if (auto p = ctx->getParent()) {
			if (cprint.trace(Trace::Name))
				cprint.trace("getNonIgnorableAncestor skipping", loc::of(ctx));
			return p;
		} else
			fatal("declaration context outside any translation unit",
				  loc::of(ctx));
	};
	if (auto p = decl.getDeclContext()) {
		for (; isIgnorableContext(*p, cprint); p = parent(p))
			;
		if (false && cprint.trace(Trace::Name)) {
			std::string what;
			llvm::raw_string_ostream os{what};
			os << "getNonIgnorableAncestor (= "
			   << loc::describe(loc::of(p), cprint.getContext()) << ")";
			cprint.trace(what, loc::of(decl));
		}
		return ref{*p};
	} else
		fatal("declaration outside any translation unit\n", loc::of(decl));
}

// Decide if a declaration is named or anonymous.
static const NamedDecl*
isNamed(const Decl& decl) {
	if (auto nd = dyn_cast<NamedDecl>(&decl))
		if (!nd->getIdentifier())
			return nullptr;
	if (auto nd = dyn_cast<NamespaceDecl>(&decl))
		return nd->isAnonymousNamespace() ? nullptr : nd;
	else if (auto crd = dyn_cast<CXXRecordDecl>(&decl)) {
		if (crd->isLambda() || crd->isAnonymousStructOrUnion())
			return nullptr;
		return crd;
	} else if (auto rd = dyn_cast<RecordDecl>(&decl))
		return rd->isAnonymousStructOrUnion() ? nullptr : rd;
	else if (auto ed = dyn_cast<EnumDecl>(&decl))
		// unnamed, scoped enums might be impossible
		return ed;
	else if (auto nd = dyn_cast<NamedDecl>(&decl))
		return nd;
	else
		return nullptr;
}

static bool
isAnonymous(const Decl& decl) {
	return isNamed(decl) == nullptr;
}

// Assign indices to anonymous declarations
static bool
getAnonymousIndex(const DeclContext& ctx, const Decl& decl, unsigned& acc,
				  ClangPrinter& cprint) {
	for (auto d : ctx.decls()) {
		if (d == &decl)
			return true;
		if (!d) {
			fatal(cprint, loc::of(ctx))
				<< "declaration context with null declaration\n";
			logging::die();
		}
		if (auto dctx = dyn_cast<DeclContext>(d)) {
			if (isIgnorableContext(*dctx, cprint) &&
				getAnonymousIndex(*dctx, decl, acc, cprint))
				return true;
		}
		if (isAnonymous(*d))
			++acc;
	}
	return false;
}

static unsigned
getAnonymousIndex(const DeclContext& ctx, const Decl& decl,
				  ClangPrinter& cprint) {
	unsigned i{0};
	if (!getAnonymousIndex(ctx, decl, i, cprint)) {
		fatal(cprint, loc::of(decl))
			<< "could not find anonymous declaration in context\n";
		logging::die();
	}
	if (false && cprint.trace(Trace::Name)) {
		std::string what;
		llvm::raw_string_ostream os{what};
		os << "getAnonymousIndex (= " << i << " )";
		cprint.trace(what, loc::of(decl));
	}
	return i;
}

static fmt::Formatter&
printTemplateParameter(CoqPrinter& print, const NamedDecl* pdecl,
					   ClangPrinter& cprint, loc::loc gloc,
					   bool as_arg = false) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printTemplateParameter", loc::of(pdecl));

	auto unsupported = [&](StringRef msg) -> auto& {
		auto loc = loc::refine(gloc, pdecl);
		::unsupported(cprint, loc) << msg << "\n";
		guard::ctor _(print, as_arg ? "Aunsupported" : "Punsupported", false);
		return print.str(msg);
	};

	if (!pdecl)
		return unsupported("null template parameter");
	auto& decl = *pdecl;

	if (decl.isParameterPack())
		return unsupported("template parameter pack");

	/*
	TODO: We could presumably infer a name for some unnamed template
	parameters.

	See `TemplateParmPosition`, `printTypeTemplateParam`.
	*/
	auto id = decl.getIdentifier();
	if (!id)
		return unsupported("unnamed template parameter");
	auto name = id->getName();

	switch (decl.getKind()) {
	case Decl::Kind::TemplateTypeParm:
		if (as_arg) {
			guard::ctor _1(print, "Atype", false);
			guard::ctor _2(print, "Tparam", false);
			return print.str(name);
		} else {
			guard::ctor _(print, "Ptype", false);
			return print.str(name);
		}

	case Decl::Kind::NonTypeTemplateParm:
		if (as_arg) {
			guard::ctor _1(print, "Avalue", false);
			guard::ctor _2(print, "Eparam", false);
			return print.str(name);
		} else {
			auto& param = cast<NonTypeTemplateParmDecl>(decl);
			guard::ctor _(print, "Pvalue", false);
			print.str(name) << fmt::nbsp;
			return cprint.printQualType(print, param.getType(), loc::of(param));
		}

	case Decl::Kind::TemplateTemplateParm:
	default:
		return unsupported("template parameter kind");
	}
}

static fmt::Formatter&
printTemplateParameters(CoqPrinter& print, const Decl& decl,
						ClangPrinter& cprint, bool as_arg) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printTemplateParameters", loc::of(decl));
	ParameterLists lists;
	if (collectParameterLists(decl, cprint.getContext(), lists)) {
		guard::list _(print);
		for (auto [params, loc] : lists)
			for (auto param : params->asArray())
				printTemplateParameter(print, param, cprint, loc, as_arg)
					<< fmt::cons;
		return print.output();
	} else
		return print.output() << "nil";
}

static fmt::Formatter&
printTemplateArgument(CoqPrinter& print, const TemplateArgument& arg,
					  ClangPrinter& cprint, loc::loc loc) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printTemplateArgument", loc);
	auto kind = arg.getKind();
	auto Avalue = [&](auto val) -> auto& {
		guard::ctor _(print, "Avalue", false);
		val();
		return print.output();
	};
	switch (kind) {
	case TemplateArgument::ArgKind::Type: {
		guard::ctor _(print, "Atype", false);
		return cprint.printQualType(print, arg.getAsType(), loc);
	}
	case TemplateArgument::ArgKind::Expression:
		return Avalue(
			[&]() { return cprint.printExpr(print, arg.getAsExpr()); });

	case TemplateArgument::ArgKind::Integral:
		return Avalue([&]() {
			guard::ctor _(print, "Eint", false);
			print.output() << arg.getAsIntegral() << fmt::nbsp;
			return cprint.printQualType(print, arg.getIntegralType(), loc);
		});

	case TemplateArgument::ArgKind::NullPtr:
		return Avalue([&]() { return print.output() << "Enull"; });

	case TemplateArgument::ArgKind::Declaration:
		/*
		TODO: Examples
		```
		struct B { int next; };
		template<int(B::*next_ptr)> struct A{};
		void test() {
		A<&B::next> a;
		}
		```
		*/
		return Avalue([&]() {
			return cprint.printValueDeclExpr(print, arg.getAsDecl());
		});

	case TemplateArgument::ArgKind::Pack: {
		guard::ctor _(print, "Apack", false);
		return print.list(arg.getPackAsArray(), [&](auto value) {
			printTemplateArgument(print, value, cprint, loc);
		});
	}
	case TemplateArgument::ArgKind::Template: {
		auto templ = arg.getAsTemplate();
		if (auto dt = templ.getAsTemplateDecl()) {
			guard::ctor _(print, "Atemplate", false);
			return cprint.printName(print, *dt);
		} /* else if (auto qtn = templ.getAsQualifiedTemplateName()) {
			return cprint.printName(print, qtn->getQualifier(), qtn->get)
		} */
		[[fallthrough]];
	}
	default: {
		auto k = templateArgumentKindName(kind);
		if (cprint.warn_well_known) {
			unsupported(cprint, loc, false)
				<< "template argument of kind " << k << "\n";
#if 19 <= CLANG_VERSION_MAJOR
			arg.dump();
#else
			arg.dump(logging::debug());
#endif
		}
		guard::ctor _(print, "Aunsupported", false);
		return print.str(k);
	}
	}
}

static fmt::Formatter&
printTemplateArgumentList(CoqPrinter& print, const TemplateArgumentList& args,
						  ClangPrinter& cprint, loc::loc loc) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printTemplateArgumentList", loc);
	return print.list(args.asArray(), [&](auto& arg) {
		printTemplateArgument(print, arg, cprint, loc);
	});
}

static const TemplateArgumentList*
recoverTemplateArgs(const Decl& decl) {
	auto sd = recoverSpecialization(decl);
	return sd ? &(sd->args) : nullptr;
}

using ArgumentLists =
	SmallVector<std::pair<const TemplateArgumentList*, loc::loc>>;

// Returns the total length of lists appended to dest
static unsigned
collectArgumentLists(const Decl& decl, const ASTContext& context,
					 ArgumentLists& dest) {
	auto n = 0;
	if (auto ctx = decl.getDeclContext()) {
		auto loc = loc::of(decl);
		auto& cdecl = cast<const Decl>(*ctx);
		n += collectArgumentLists(cdecl, context, dest);
		if (auto args = recoverTemplateArgs(decl)) {
			n += args->size();
			dest.push_back(std::make_pair(args, loc));
		}
	}
	return n;
}

static fmt::Formatter&
printTemplateArguments(CoqPrinter& print, const Decl& decl,
					   ClangPrinter& cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printTemplateArguments", loc::of(decl));
	ArgumentLists lists;
	if (collectArgumentLists(decl, cprint.getContext(), lists)) {
		guard::list _(print);
		for (auto [args, loc] : lists)
			for (auto arg : args->asArray())
				printTemplateArgument(print, arg, cprint, loc) << fmt::cons;
		return print.output();
	} else
		return print.output() << "nil";
}

static fmt::Formatter&
printFunctionQualifiers(CoqPrinter& print, const FunctionDecl& decl,
						ClangPrinter& cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printFunctionQualifiers", loc::of(decl));
	const char* const_volatile_cat[2][2][3] = {
		{{"N", "Nl", "Nr"}, {"Nv", "Nvl", "Nvr"}},
		{{"Nc", "Ncl", "Ncr"}, {"Ncv", "Ncvl", "Ncvr"}}};

	if (auto md = dyn_cast<CXXMethodDecl>(&decl)) {
		static_assert(RefQualifierKind::RQ_None == 0);
		static_assert(RefQualifierKind::RQ_LValue == 1);
		static_assert(RefQualifierKind::RQ_RValue == 2);
		return print.output()
			   << "function_qualifiers."
			   << const_volatile_cat[md->isConst()][md->isVolatile()]
									[md->getRefQualifier()];
	} else {
		return print.output() << "function_qualifiers.N";
	}

	return print.output();
}

static fmt::Formatter&
printFunctionName(CoqPrinter& print, const FunctionDecl& decl,
				  ClangPrinter& cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printFunctionName", loc::of(decl));
	auto unsupported = [&]() -> auto& {
		std::string what;
		llvm::raw_string_ostream os{what};
		os << "function name: ";
		decl.getNameForDiagnostic(os, cprint.getContext().getPrintingPolicy(),
								  false);
		::unsupported(cprint, loc::of(decl)) << what << "\n";
		guard::ctor _(print, "Nunsupported_function", false);
		return print.str(what);
	};
	auto name = decl.getDeclName();
	switch (name.getNameKind()) {

	case DeclarationName::NameKind::Identifier:
		if (auto id = name.getAsIdentifierInfo()) {
			guard::ctor _(print, "Nf", false);
			return print.str(id->getName());
		} else
			return unsupported();

	case DeclarationName::NameKind::CXXConstructorName:
		return print.output() << "Nctor";

	case DeclarationName::NameKind::CXXDestructorName:
		return print.output() << "Ndtor";

	case DeclarationName::NameKind::CXXOperatorName: {
		guard::ctor _(print, "Nop", false);
		return cprint.printOverloadableOperator(
			print, name.getCXXOverloadedOperator(), loc::of(decl));
	}

	case DeclarationName::NameKind::CXXConversionFunctionName: {
		guard::ctor _(print, "Nop_conv", false);
		return cprint.printQualType(print, name.getCXXNameType(),
									loc::of(decl));
	}

	case DeclarationName::NameKind::CXXLiteralOperatorName:
		if (auto id = name.getCXXLiteralIdentifier()) {
			guard::ctor _(print, "Nop_lit", false);
			return print.str(id->getName()) << fmt::nbsp;
		} else
			return unsupported();

	default:
		return unsupported();
	}
}

static fmt::Formatter&
printFunctionParamTypes(CoqPrinter& print, const FunctionDecl& decl,
						ClangPrinter& cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printFunctionParamTypes", loc::of(decl));
	auto loc = loc::of(decl);
	return print.list(decl.parameters(), [&](auto* param) {
		cprint.printQualType(print, param->getType(), loc);
	});
}

static fmt::Formatter&
printAtomicName(const DeclContext& ctx, const Decl& decl, CoqPrinter& print,
				ClangPrinter& cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printAtomicName", loc::of(decl));

	auto unsupported = [&](StringRef what) -> auto& {
		::unsupported(cprint, loc::of(decl)) << what << "\n";
		guard::ctor ctor(print, "Nunsupported_atomic", false);
		return print.str(what);
	};
	auto ident = [&]() -> auto& {
		if (auto nd = isNamed(decl)) {
			guard::ctor _(print, "Nid", false);
			return print.str(nd->getName());
		}
		always_assert(false && "ident for un-named term");
		return unsupported("ident for un-named term");
	};

	auto ident_or_anon = [&](const std::optional<std::string> anon_error =
								 std::nullopt) -> auto& {
		if (auto nd = isNamed(decl)) {
			guard::ctor _(print, "Nid", false);
			return print.str(nd->getName());
		} else if (!anon_error) {
			guard::ctor _(print, "Nanon", false);
			return print.output() << getAnonymousIndex(ctx, decl, cprint);
		} else
			return unsupported(anon_error.value());
	};
	auto by_first_decl = [&](const TagDecl* decl) {
		// this heuristic tries to construct a name using the first declaration
		// that has that type. For example,
		//
		//  struct { } x;
		//
		// the name of the struct is essentially [decltype(x)].
		for (auto by_decl = decl->getNextDeclInContext(); by_decl;
			 by_decl = by_decl->getNextDeclInContext()) {
			if (auto vd = dyn_cast<ValueDecl>(by_decl)) {
				auto type = vd->getType().getTypePtr();
				if (type->getAsTagDecl() == decl && vd->getIdentifier()) {
					guard::ctor _(print, "Nby_first_decl", false);
					print.str(vd->getIdentifier()->getName());
					return true;
				}
				break;
			}
			// This returns [false] if [by_decl] is not a lexical child of [decl]
			for (auto i = by_decl->getLexicalDeclContext(); i;
				 i = i->getParent()) {
				if (i->isTranslationUnit())
					return false;
			}
		}
		return false;
	};

	if (auto td = dyn_cast<TagDecl>(&decl)) {
		if (isNamed(*td)) {
			return ident();
		}
		if (auto type_def = td->getTypedefNameForAnonDecl()) {
			guard::ctor _(print, "Nid", false);
			return print.str(type_def->getName());
		}
		if (by_first_decl(td))
			return print.output();
	}
	if (auto rd = dyn_cast<RecordDecl>(&decl)) {
		if (rd->getParent()->isTranslationUnit()) {
			logging::unsupported()
				<< "Anonymous global records without declarations are not "
				   "supported. These can not be referenced in C++!\n "
				<< fmt::dump(*rd);
			return unsupported("record");
		}
		for (auto i : rd->fields()) {
			if (i->getIdentifier()) {
				guard::ctor _(print, "Nrecord_by_field", false);
				return print.str(i->getIdentifier()->getName());
			}
		}
	} else if (auto ed = dyn_cast<EnumDecl>(&decl)) {
		for (auto i : ed->enumerators()) {
			if (i->getIdentifier()) {
				guard::ctor _(print, "Nenum_by_enumerator", false);
				return print.str(i->getIdentifier()->getName());
			}
		}
		if (ed->getParent()->isTranslationUnit()) {
			logging::unsupported() << "Unsupported empty enumeration in global "
									  "context. These can not be "
									  "referenced in C++!\n"
								   << fmt::dump(*ed);
			return unsupported("enum");
		}
	} else if (auto ns = dyn_cast<NamespaceDecl>(&decl)) {
		if (isNamed(*ns)) {
			return ident();
		}
		return print.output() << "Nanonymous";
		/*
		for (auto i : ns->decls()) {
			if (auto nd = dyn_cast<NamedDecl>(i)) {
				if (nd->getIdentifier()) {
					guard::ctor _(print, "Nnamespace_by_decl", false);
					return print.str(nd->getIdentifier()->getName());
				}
			}
		} */
	}

	switch (decl.getKind()) {
	case Decl::Kind::Namespace:
	case Decl::Kind::Record:
	case Decl::Kind::CXXRecord:
	case Decl::Kind::Enum:
	case Decl::Kind::TypeAlias:
	case Decl::Kind::Typedef:
	case Decl::Kind::ClassTemplate:
		return ident_or_anon();

	case Decl::Kind::Field:
		/*
		TODO: Other parts of cpp2v emit anonymous fields using
		<<field_name.t>>. Here, we use <<Nanon>>.
		*/
		return ident_or_anon();

	case Decl::Kind::FunctionTemplate: {
		auto& fd = *cast<FunctionTemplateDecl>(decl).getTemplatedDecl();
		guard::ctor _(print, "Nfunction", false);
		printFunctionQualifiers(print, fd, cprint) << fmt::nbsp;
		printFunctionName(print, fd, cprint) << fmt::nbsp;
		return printFunctionParamTypes(print, fd, cprint);
	}
	case Decl::Kind::Function:
	case Decl::Kind::CXXMethod:
	case Decl::Kind::CXXConstructor:
	case Decl::Kind::CXXDestructor:
	case Decl::Kind::CXXConversion: {
		auto& fd = cast<FunctionDecl>(decl);
		guard::ctor _(print, "Nfunction", false);
		printFunctionQualifiers(print, fd, cprint) << fmt::nbsp;
		printFunctionName(print, fd, cprint) << fmt::nbsp;
		return printFunctionParamTypes(print, fd, cprint);
	}

	case Decl::Kind::TypeAliasTemplate:
	case Decl::Kind::VarTemplate:
	case Decl::Kind::VarTemplateSpecialization:
	case Decl::Kind::VarTemplatePartialSpecialization:
		return ident_or_anon("anonymous template");

	case Decl::Kind::Var:
		return ident_or_anon("anonymous variable");

	case Decl::Kind::EnumConstant:
		/*
		Enum constant names should not arise in practice (see
		`Eenum_const`). They're supported here for `--test-name`.
		*/
		return ident_or_anon("anonymous enum constant");
		// TODO: Ndecltype
		// TODO: Nclosure
	case Decl::Kind::Binding:
		return ident_or_anon("anonymous binding");
	default:
		std::string what;
		llvm::raw_string_ostream os{what};
		os << "atomic name of kind " << decl.getDeclKindName();
		return unsupported(what);
	}
}

static fmt::Formatter& printName(CoqPrinter&, const Decl&, ClangPrinter&);

static fmt::Formatter&
printName(CoqPrinter& print, const Decl& decl, ClangPrinter& cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("structured::printName", loc::of(decl));
	if (auto nd = dyn_cast<NamedDecl>(&decl)) {
		if (print.reference(nd))
			return print.output();
	} else {
		llvm::errs() << "not a named decl\n";
		decl.dump();
		always_assert(false);
	}

	if (auto sd = recoverSpecialization(decl)) {
		// Printing template specializations should print
		// <<Ninst (templated-name) [template-arguments]>>
		guard::ctor _(print, "Ninst", false);
		printName(print, sd->temp, cprint) << fmt::line;
		return printTemplateArgumentList(print, sd->args, cprint,
										 loc::of(decl));
	} else {
		auto ctx = getNonIgnorableAncestor(decl, cprint);
		auto atomic = [&]() -> auto& {
			return printAtomicName(ctx, decl, print, cprint);
		};
		if (ctx->isTranslationUnit()) {
			guard::ctor _(print, "Nglobal", false);
			return atomic();
		} else {
			guard::ctor _(print, "Nscoped", false);
			cprint.printName(print, toDecl(ctx, cprint, loc::of(decl)))
				<< fmt::nbsp;
			return atomic();
		}
	}
}

#if 0
template<typename DERIVED, typename RetTy>
struct NameVisitor {
	RetTy Visit(const Decl* decl) {
		auto self = static_cast<DERIVED*>(this);
		if (auto sd = recoverSpecialization(decl)) {
			return self->VisitInst(decl, sd->temp, sd->args);
		}
		auto ctx = getNonIgnorableAncestor(decl);
		if (auto nd = dyn_cast<NamedDecl>(decl)) {
			if (ctx->isTranslationUnit()) {
				return self->VisitScoped(ctx, decl, true);
			} else {
				return self->VisitScoped(ctx, decl, false);
			}
		} else {
			llvm::errs() << "decl is not named (" << decl->getDeclKindName()
						 << ")\n";
			always_assert(false && "unnamed decl");
		}
	}

	RetTy Visit(const DeclContext* dc) {
		auto self = static_cast<DERIVED*>(this);
		if (auto tu = dyn_cast<TranslationUnitDecl>(dc))
			return self->VisitTU(tu);
		if (auto d = dyn_cast<Decl>(dc)) {
			return self->Visit(d);
		} else
			return self->Visit(dc->getParent())
	}

	// For override
	RetTy VisitName(const NamedDecl*) {
		return RetTy{};
	}

	RetTy VisitTU(const TranslationUnitDecl*) {
		return Ty{};
	}

	RetTy VisitInst(const Decl* whole, const TemplateDecl*,
					TemplateArgumentList&) {
		return VisitName(whole);
	}
	RetTy VisitScoped(const DeclContext*, const NamedDecl* decl, bool global) {
		return VisitName(decl);
	}

	ClangPrinter& cprint_;
};

struct PrintName : NameVisitor<PrintName, void> {

	void VisitScoped(const DeclContext* ctx, const NamedDecl* decl,
					 bool global) {
		auto atomic = [&]() -> auto {
			printAtomicName(*ctx, *decl, print, cprint);
		};
		if (global) {
			guard::ctor _(print, "Nglobal", false);
			return atomic();
		} else {
			guard::ctor _(print, "Nscoped", false);
			Visit(ctx);
			print.output() << fmt::nbsp;
			return atomic();
		}
	}

	void VisitInst(const Decl* whole, const TemplateDecl* temp,
				   TemplateArgumentList& args) {
		guard::ctor _(print, "Ninst", false);
		Visit(temp);
		print.output() << fmt::nbsp;
		printTemplateArgumentList(print, args, cprint, loc::of(decl));
	}

	ClangPrinter& cprint;
	CoqPrinter& print;
};
#endif

static fmt::Formatter&
printDtorName(CoqPrinter& print, const CXXRecordDecl& decl,
			  ClangPrinter& cprint) {
	if (ClangPrinter::debug && cprint.trace(Trace::Name))
		cprint.trace("printDtorName", loc::of(decl));

	guard::ctor _(print, "Nscoped", false);
	printName(print, decl, cprint) << fmt::nbsp;
	{
		guard::ctor _(print, "Nfunction", false);
		return print.output() << "function_qualifiers.N" << fmt::nbsp << "Ndtor"
							  << fmt::nbsp << "nil";
	}
}

} // namespace structured

template<typename T>
T&
deref(CoqPrinter& print, ClangPrinter& cprint, const std::string whence, T* p,
	  loc::loc loc) {
	if (!p) {
		fatal(cprint, loc) << whence << ": null pointer\n";
		print.die();
	}
	return *p;
}

fmt::Formatter&
ClangPrinter::printNameComment(CoqPrinter& print, const Decl& decl) {
	if (trace(Trace::Name))
		trace("printNameComment", loc::of(decl));
	if (comment_)
		if (auto nd = dyn_cast<NamedDecl>(&decl)) {
			std::string cmt;
			llvm::raw_string_ostream os{cmt};
			structured::printNameForDiagnostics(os, *nd, getContext());
			return print.cmt(cmt);
		}
	return print.output();
}

fmt::Formatter&
ClangPrinter::printNameAsKey(CoqPrinter& print, const Decl& decl) {
	if (trace(Trace::Name))
		trace("printNameAsKey", loc::of(decl));
	if (print.structured_keys())
		return printName(print, decl);
	else
		return mangled::printName(print, decl, *this);
}

fmt::Formatter&
ClangPrinter::printNameAsKey(CoqPrinter& print, const Decl* p, loc::loc loc) {
	return printNameAsKey(print, deref(print, *this, "printNameAsKey", p, loc));
}

fmt::Formatter&
ClangPrinter::printName(CoqPrinter& print, const Decl& decl, bool full) {
	if (trace(Trace::Name))
		trace("printName", loc::of(decl));
	if (full) {
		auto temp = withDecl(&decl);
		return structured::printName(print, decl, temp);
	} else
		return structured::printAtomicName(*(decl.getDeclContext()), decl,
										   print, *this);
}

fmt::Formatter&
ClangPrinter::printName(CoqPrinter& print, const Decl* p, loc::loc loc,
						bool full) {
	return printName(print, deref(print, *this, "printName", p, loc), full);
}

fmt::Formatter&
ClangPrinter::printName(CoqPrinter& print, const NestedNameSpecifier* spec,
						loc::loc loc) {
	if (auto ns = spec->getAsNamespace()) {
		printName(print, ns, loc);
	} else if (auto nsa = spec->getAsNamespaceAlias()) {
		printName(print, nsa, loc);
	} else if (auto type = spec->getAsType()) {
		guard::ctor _(print, "Ndependent", false);
		printType(print, type, loc);
	} else if (auto id = spec->getAsIdentifier()) {
		bool is_global = not spec->getPrefix() ||
						 spec->getPrefix()->getKind() ==
							 NestedNameSpecifier::SpecifierKind::Global;

		guard::ctor _(print, is_global ? "Nglobal" : "Nscoped", false);
		if (not is_global) {
			printName(print, spec->getPrefix(), loc);
			print.output() << fmt::nbsp;
		}
		guard::ctor __(print, "Nid", false);
		print.output() << "\"" << id->getName() << "\"";
	} else {
		llvm::errs() << "unknown NestedNameSpecifier(" << spec->getKind()
					 << ")\n";
		llvm::errs().flush();
	}
	return print.output();
}

fmt::Formatter&
ClangPrinter::printUnsupportedName(CoqPrinter& print, StringRef msg) {
	guard::ctor _(print, "Nunsupported", false);
	return print.str(msg);
}

fmt::Formatter&
ClangPrinter::printDtorName(CoqPrinter& print, const CXXRecordDecl& decl) {
	if (trace(Trace::Name))
		trace("printDtorName", loc::of(decl));
	return structured::printDtorName(print, decl, *this);
}

fmt::Formatter&
ClangPrinter::printUnqualifiedName(CoqPrinter& print, const NamedDecl& decl) {
	if (trace(Trace::Name))
		trace("printUnqualifiedName", loc::of(decl));
	if (auto id = decl.getIdentifier())
		return print.str(id->getName());
	else {
		unsupported(*this, loc::of(decl)) << "unnamed, unqualified name\n";
		return print.str("<unsupported unnamed, unqualified name>");
	}
}

fmt::Formatter&
ClangPrinter::printUnqualifiedName(CoqPrinter& print, const NamedDecl* p,
								   loc::loc loc) {
	return printUnqualifiedName(
		print, deref(print, *this, "printUnqualifiedName", p, loc));
}

fmt::Formatter&
ClangPrinter::printTemplateParameters(CoqPrinter& print, const Decl& decl,
									  bool as_arg) {
	if (trace(Trace::Name))
		trace("printTemplateParameters", loc::of(decl));
	return structured::printTemplateParameters(print, decl, *this, as_arg);
}

fmt::Formatter&
ClangPrinter::printTemplateArguments(CoqPrinter& print, const Decl& decl) {
	if (trace(Trace::Name))
		trace("printTemplateArguments", loc::of(decl));
	return structured::printTemplateArguments(print, decl, *this);
}

fmt::Formatter&
ClangPrinter::printTemplateArgumentList(CoqPrinter& print,
										const TemplateArgumentList& args,
										loc::loc loc) {
	if (trace(Trace::Name))
		trace("printTemplateArgumentList", loc);
	return structured::printTemplateArgumentList(print, args, *this, loc);
}

fmt::Formatter&
ClangPrinter::printTemplateArgumentList(CoqPrinter& print,
										ArrayRef<TemplateArgument> args) {
	if (trace(Trace::Name))
		trace("printTemplateArgumentList", loc::none);
	auto& cprint = *this;
	return print.list(args, [&](auto& arg) {
		structured::printTemplateArgument(print, arg, cprint, loc::none);
	});
}

fmt::Formatter&
ClangPrinter::printTemplateArgumentList(CoqPrinter& print,
										ArrayRef<TemplateArgumentLoc> args) {
	if (trace(Trace::Name))
		trace("printTemplateArgumentList", loc::none);
	auto& cprint = *this;
	return print.list(args, [&](auto& arg) {
		structured::printTemplateArgument(print, arg.getArgument(), cprint,
										  loc::of(arg));
	});
}

namespace {
fmt::Formatter&
printDeclarationName(CoqPrinter& print, const DeclarationName& name,
					 ClangPrinter& cprint) {
	/*
		TODO: This seems

		- A bit limited --- compare to/share code with structured::printFunctionName

		- A bit off --- `name.getAsString` does not account for `Ndtor` etc
		*/
	switch (name.getNameKind()) {
	case DeclarationName::NameKind::Identifier: {
		/*
			Example: A function name that couldn't be resolved due to an
			argument depending on a template parameter.
			*/

		auto atomic = [&]() -> fmt::Formatter& {
			{
				guard::ctor _(print, "Nfunction", false);
				print.output() << "function_qualifiers.N" << fmt::nbsp;
				{
					guard::ctor _(print, "Nf", false);
					print.str(name.getAsString());
				}
				return print.output() << fmt::nbsp << "nil";
			}
		};

		atomic();
		break;
	}

	default:
		llvm::errs() << "printDeclarationName(" << name.getNameKind() << ")";
		name.dump();
		print.output() << "(Nunsupported \"printDeclarationName("
					   << name.getNameKind() << ")\")";
	}
	return print.output();
}
}

fmt::Formatter&
ClangPrinter::printUnresolvedName(
	CoqPrinter& print, const NestedNameSpecifier* nn,
	const DeclarationName& name,
	llvm::ArrayRef<clang::TemplateArgumentLoc> template_args, loc::loc loc) {
	if (not nn) {
		guard::ctor _(print, "Nglobal", false);
		return printDeclarationName(print, name, *this);
	} else if (nn->getKind() == NestedNameSpecifier::Global) {
		guard::ctor _(print, "Nglobal", false);
		return printDeclarationName(print, name, *this);
	} else {
		guard::ctor _(print, "Nscoped", false);
		printName(print, nn, loc) << fmt::nbsp;
		return printDeclarationName(print, name, *this);
	}
}

fmt::Formatter&
ClangPrinter::printUnresolvedName(CoqPrinter& print,
								  const NestedNameSpecifier* nn,
								  const IdentifierInfo& name, loc::loc loc) {
	if (not nn) {
		guard::ctor _(print, "Nglobal", false);
		print.output() << '\"' << name.getName() << '\n';
		return print.output();
	} else if (nn->getKind() == NestedNameSpecifier::Global) {
		guard::ctor _(print, "Nglobal", false);
		print.output() << '\"' << name.getName() << '\n';
		return print.output();
	} else {
		guard::ctor _(print, "Nscoped", false);
		printName(print, nn, loc) << fmt::nbsp;
		{
			guard::ctor __{print, "Nid", false};
			print.str(name.getName());
		}
		return print.output();
	}
}
