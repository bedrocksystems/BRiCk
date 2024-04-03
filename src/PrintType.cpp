/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Logging.hpp"
#include "TypeVisitorWithArgs.h"
#include "config.hpp"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/Type.h"
#include <Formatter.hpp>

using namespace clang;
using namespace fmt;

[[noreturn]] static void
fatal(CoqPrinter& print, ClangPrinter& cprint, loc::loc loc, StringRef msg) {
	cprint.error_prefix(logging::fatal(), loc) << "error: " << msg << "\n";
	cprint.debug_dump(loc);
	print.die();
}

static void
unsupported(CoqPrinter& print, ClangPrinter& cprint, loc::loc loc,
			const Twine& msg, bool well_known = false) {
	if (!well_known || ClangPrinter::warn_well_known) {
		cprint.error_prefix(logging::unsupported(), loc)
			<< "warning: unsupported " << msg << "\n";
		cprint.debug_dump(loc);
	}
	guard::ctor _(print, "Tunsupported", false);
	{
		std::string coqmsg;
		llvm::raw_string_ostream os{coqmsg};
		os << loc::describe(loc, cprint.getContext());
		print.str(coqmsg);
	}
}

static void
unsupported_type(CoqPrinter& print, ClangPrinter& cprint, const Type* type,
				 bool well_known = false) {
	unsupported(print, cprint, loc::of(type), "type", well_known);
}

class PrintType :
	public TypeVisitor<PrintType, void, CoqPrinter&, ClangPrinter&> {
private:
	PrintType() {}

public:
	static PrintType printer;

	void VisitType(const Type* type, CoqPrinter& print, ClangPrinter& cprint) {
		unsupported_type(print, cprint, type);
	}

#define IGNORE(T)                                                              \
	void Visit##T(const T* type, CoqPrinter& print, ClangPrinter& cprint) {    \
		unsupported_type(print, cprint, type, /*well_known*/ true);            \
	}

	// Several of these are template TODOs

	IGNORE(BlockPointerType)
	IGNORE(DependentNameType)
	IGNORE(DependentSizedArrayType)
	IGNORE(PackExpansionType)

	void VisitAttributedType(const AttributedType* type, CoqPrinter& print,
							 ClangPrinter& cprint) {
		cprint.printQualType(type->getModifiedType(), print, loc::of(type));
	}

	static const char* getTransformName(UnaryTransformType::UTTKind k) {
		switch (k) {
#define TRANSFORM_TYPE_TRAIT_DEF(Enum, Str)                                    \
	case UnaryTransformType::UTTKind::Enum:                                    \
		return #Str;
#include "clang/Basic/TransformTypeTraits.def"
#undef TRANSFORM_TYPE_TRAIT_DEF
		default:
			return "unknown";
		}
	}

	void VisitUnaryTransformType(const UnaryTransformType* type,
								 CoqPrinter& print, ClangPrinter& cprint) {
		if (type->isDependentType()) {
			// TODO: templates
			unsupported_type(print, cprint, type,
							 /*well_known*/ true);
			return;
		}

		switch (auto kind = type->getUTTKind()) {
		case UnaryTransformType::UTTKind::EnumUnderlyingType:

			// An `__underlying_type (type)` expression
			// where `type` is a scoped enumeration type.
			//
			// See:
			//
			// https://en.cppreference.com/w/cpp/utility/to_underlying
			// https://gcc.gnu.org/onlinedocs/gcc-11.1.0/gcc/Type-Traits.html

			print.ctor("@Tunderlying", false);
			print.type() << fmt::nbsp;
			break;

		default:
			print.ctor("@Tunary_xform", false);
			print.type() << fmt::nbsp;

			print.str(getTransformName(kind));
			print.output() << "%bs" << fmt::nbsp;
			break;
		}

		// The argument
		cprint.printQualType(type->getBaseType(), print, loc::of(type));
		print.output() << fmt::nbsp;

		// The result (can be null if dependent)
		cprint.printQualType(type->getUnderlyingType(), print, loc::of(type));
		print.end_ctor();
	}

	void VisitAutoType(const AutoType* type, CoqPrinter& print,
					   ClangPrinter& cprint) {
		if (type->isDeduced() && !type->isDependentType()) {
			cprint.printQualType(type->getDeducedType(), print, loc::of(type));
		} else {
			if (print.templates())
				print.output() << "Tauto";
			else
				unsupported_type(print, cprint, type, /*well_known*/ true);
		}
	}

	void VisitDeducedType(const DeducedType* type, CoqPrinter& print,
						  ClangPrinter& cprint) {
		if (type->isDeduced()) {
			cprint.printQualType(type->getDeducedType(), print, loc::of(type));
		} else {
			unsupported_type(print, cprint, type);
		}
	}

	void VisitTemplateTypeParmType(const TemplateTypeParmType* type,
								   CoqPrinter& print, ClangPrinter& cprint) {
		print.ctor(print.ast2() ? "Tparam" : "Tvar", false);
		if (auto ident = type->getIdentifier()) {
			print.str(ident->getName());
		} else {
			cprint.printNameForAnonTemplateParam(
				type->getDepth(), type->getIndex(), print, loc::of(type));
		}
		print.end_ctor();
	}

	void VisitEnumType(const EnumType* type, CoqPrinter& print,
					   ClangPrinter& cprint) {
		auto ed = type->getDecl()->getCanonicalDecl();
		print.ctor("Tenum", false);
		cprint.printTypeName(ed, print, loc::of(type));
		print.end_ctor();
	}

	void VisitRecordType(const RecordType* type, CoqPrinter& print,
						 ClangPrinter& cprint) {
		print.ctor("Tnamed", false);
		cprint.printTypeName(type->getDecl(), print, loc::of(type));
		print.end_ctor();
	}

	void VisitParenType(const ParenType* type, CoqPrinter& print,
						ClangPrinter& cprint) {
		cprint.printQualType(type->getInnerType(), print, loc::of(type));
	}

	void VisitBuiltinType(const BuiltinType* type, CoqPrinter& print,
						  ClangPrinter& cprint) {
		switch (type->getKind()) {
#define CASE(x, str)                                                           \
	case BuiltinType::Kind::x:                                                 \
		print.output() << str;                                                 \
		break;
			CASE(Bool, "Tbool")
			CASE(Void, "Tvoid")
			CASE(NullPtr, "Tnullptr")
			CASE(SChar, "Tschar")
			CASE(UChar, "Tuchar")
			// Both [Char_S] and [Char_U] are representations of the C++ 'char'
			// type, but are used depending on the platform's choice of whether
			// 'char' is signed or not.
			CASE(Char_S, "Tchar")
			CASE(Char_U, "Tchar")
			CASE(WChar_S, "Twchar")
			CASE(WChar_U, "Twchar")
			CASE(Char16, "Tchar16")
			CASE(Char32, "Tchar32")
			CASE(Char8, "Tchar8")
			CASE(Short, "Tshort")
			CASE(UShort, "Tushort")
			CASE(Int, "Tint")
			CASE(UInt, "Tuint")
			CASE(Long, "Tlong")
			CASE(ULong, "Tulong")
			CASE(LongLong, "Tlonglong")
			CASE(ULongLong, "Tulonglong")
			CASE(Int128, "Ti128")
			CASE(UInt128, "Tu128")
			CASE(Float, "Tfloat")
			CASE(Double, "Tdouble")
			CASE(LongDouble, "Tlongdouble")
#undef CASE
		case BuiltinType::Kind::Dependent:
			if (print.templates()) {
				// TODO: Placeholder
				print.output() << "Tdependent";
			} else if (false) {
				// We prefer to keep going with Tunsupported
				using namespace logging;
				fatal()
					<< "Clang failed to resolve type, due to earlier errors or "
					   "unresolved templates\n"
					<< "Try fixing earlier errors, or ask for help. Aborting\n";
				die();
			} else
				unsupported_type(print, cprint, type, /*well_known*/ true);
			break;

		default:
			if (type->isAnyCharacterType()) {
				assert(false && "unexpected character type");
			} else if (type->isFloatingPoint()) {
				assert(false && "unexpected floating point type");
			} else if (type->isIntegerType()) {
				assert(false);
			} else if (type->isSizelessBuiltinType()) {
				// TODO: This seems a bit random. Do we need
				// another type constructor?
				print.output() << fmt::lparen << "Tarch None \""
							   << type->getNameAsCString(
									  cprint.getContext().getPrintingPolicy())
							   << "\"" << fmt::rparen;
				break;
			} else {
				unsupported_type(print, cprint, type);
			}
		}
	}

	void VisitLValueReferenceType(const LValueReferenceType* type,
								  CoqPrinter& print, ClangPrinter& cprint) {
		print.ctor("Tref", false);
		cprint.printQualType(type->getPointeeType(), print, loc::of(type));
		print.end_ctor();
	}

	void VisitRValueReferenceType(const RValueReferenceType* type,
								  CoqPrinter& print, ClangPrinter& cprint) {
		print.ctor("Trv_ref", false);
		cprint.printQualType(type->getPointeeType(), print, loc::of(type));
		print.end_ctor();
	}

	void VisitPointerType(const PointerType* type, CoqPrinter& print,
						  ClangPrinter& cprint) {
		print.ctor("Tptr", false);
		cprint.printQualType(type->getPointeeType(), print, loc::of(type));
		print.end_ctor();
	}

	void VisitTypedefType(const TypedefType* type, CoqPrinter& print,
						  ClangPrinter& cprint) {
		if (PRINT_ALIAS) {
			print.ctor("@Talias", false);
			print.type() << fmt::nbsp;
			print.output() << "\"";
			cprint.printTypeName(type->getDecl(), print, loc::of(type));
			// printing a "human readable" type
			// type->getDecl()->printQualifiedName(print.output().nobreak());
			print.output() << "\"" << fmt::nbsp;
			cprint.printQualType(
				type->getDecl()->getCanonicalDecl()->getUnderlyingType(), print,
				loc::of(type));
			print.end_ctor();
		} else {
			cprint.printQualType(
				type->getDecl()->getCanonicalDecl()->getUnderlyingType(), print,
				loc::of(type));
		}
	}

	void VisitFunctionProtoType(const FunctionProtoType* type,
								CoqPrinter& print, ClangPrinter& cprint) {
		print.ctor("@Tfunction");
		cprint.printCallingConv(type->getCallConv(), print, loc::of(type));
		print.output() << fmt::nbsp;
		cprint.printVariadic(type->isVariadic(), print);
		print.output() << fmt::nbsp;
		cprint.printQualType(type->getReturnType(), print, loc::of(type));
		print.output() << fmt::nbsp;
		print.list(type->param_types(), [&](auto i) {
			cprint.printQualType(i, print, loc::of(type));
		});
		print.end_ctor();
	}

	void VisitElaboratedType(const ElaboratedType* type, CoqPrinter& print,
							 ClangPrinter& cprint) {
		cprint.printQualType(type->getNamedType(), print, loc::of(type));
	}

	void VisitConstantArrayType(const ConstantArrayType* type,
								CoqPrinter& print, ClangPrinter& cprint) {
		print.ctor("Tarray");
		cprint.printQualType(type->getElementType(), print, loc::of(type));
		print.output() << fmt::nbsp << type->getSize().getLimitedValue();
		print.end_ctor();
	}

	void VisitSubstTemplateTypeParmType(const SubstTemplateTypeParmType* type,
										CoqPrinter& print,
										ClangPrinter& cprint) {
		cprint.printQualType(type->getReplacementType(), print, loc::of(type));
	}

	void VisitIncompleteArrayType(const IncompleteArrayType* type,
								  CoqPrinter& print, ClangPrinter& cprint) {
		print.ctor("Tincomplete_array");
		cprint.printQualType(type->getElementType(), print, loc::of(type));
		print.end_ctor();
	}

	void VisitVariableArrayType(const VariableArrayType* type,
								CoqPrinter& print, ClangPrinter& cprint) {
		print.ctor("Tvariable_array");
		cprint.printQualType(type->getElementType(), print, loc::of(type));
		print.output() << fmt::nbsp;
		cprint.printExpr(type->getSizeExpr(), print);
		print.end_ctor();
	}

	void VisitDecayedType(const DecayedType* type, CoqPrinter& print,
						  ClangPrinter& cprint) {
		print.ctor("Tdecay_type");
		cprint.printQualType(type->getOriginalType(), print, loc::of(type));
		print.output() << fmt::nbsp;
		cprint.printQualType(type->getAdjustedType(), print, loc::of(type));
		print.end_ctor();
	}

	fmt::Formatter& printRiskyTypeComment(const Type* type, CoqPrinter& print,
										  ClangPrinter& cprint) {
		if (ClangPrinter::debug && cprint.trace(Trace::Type)) {
			auto loc = loc::of(type);
			cprint.trace("printRiskyTypeComment", loc);
			std::string cmt;
			llvm::raw_string_ostream os{cmt};
			auto& context = cprint.getContext();
			os << "risky type";
			if (loc::can_describe(loc))
				os << ": " << loc::describe(loc, context);
			cprint.error_prefix(logging::unsupported(), loc)
				<< "warning: " << cmt << "\n";
			return print.cmt(cmt);
		} else
			return print.output();
	}

	void VisitTemplateSpecializationType(const TemplateSpecializationType* type,
										 CoqPrinter& print,
										 ClangPrinter& cprint) {
		auto unsupported = [&]() {
			unsupported_type(print, cprint, type, /*well_known*/ true);
		};
		if (type->isSugared()) {
			cprint.printQualType(type->desugar(), print, loc::of(type));
		} else if (print.ast2()) {
			/*
            TODO: See the comment in VisitInjectedClassNameType. We
            probably have to print the entire specialized scope, and not
            just this type.
            */
			auto temp = type->getTemplateName().getAsTemplateDecl();
			auto args = type->template_arguments();
			if (temp) {
				printRiskyTypeComment(type, print, cprint) << fmt::nbsp;
				guard::ctor _1(print, "Tnamed");
				guard::ctor _2(print, "Ninst");
				cprint.printStructuredName(*temp, print) << fmt::nbsp;
				cprint.printTemplateArgumentList(args, print);
			} else
				unsupported();
		} else
			unsupported();
	}

	void VisitDecltypeType(const DecltypeType* type, CoqPrinter& print,
						   ClangPrinter& cprint) {
		if (type->isSugared()) {
			// The guard ensure the type visitor terminates.
			cprint.printQualType(type->desugar(), print, loc::of(type));
		} else if (print.templates()) {
			cprint.printQualType(type->getUnderlyingType(), print,
								 loc::of(type));
		} else
			unsupported_type(print, cprint, type, /*well_known*/ true);
	}

	void VisitTypeOfExprType(const TypeOfExprType* type, CoqPrinter& print,
							 ClangPrinter& cprint) {
		if (type->isSugared()) {
			// The guard ensure the type visitor terminates.
			cprint.printQualType(type->desugar(), print, loc::of(type));
		} else if (print.templates()) {
			/*
            TODO: Test whether we need printQualTypeOption here.
            */
			cprint.printQualType(type->getUnderlyingExpr()->getType(), print,
								 loc::of(type));
		} else {
			unsupported_type(print, cprint, type);
		}
	}

	void VisitInjectedClassNameType(const InjectedClassNameType* type,
									CoqPrinter& print, ClangPrinter& cprint) {
		auto nodecl = [&]() {
			unsupported(print, cprint, loc::of(type),
						"injected class name without declaration");
		};
		if (print.templates() && print.ast2()) {
			if (auto decl = type->getDecl()) {
				/*
                TODO: We probably have to make this smarter.

                Cobble up some examples and decide if there is a problem
                with always synthesizing arguments.

                Example idea: Print the type of a template in a
                (partially) specialized scope.

                Algorithm idea: We probably have have to walk up the
                declaration context chain, collecting a list of
                `TemplateArgument + TemplateParameter` entries, and
                synthesizing only those arguments that are "missing".
                */
				printRiskyTypeComment(type, print, cprint) << fmt::nbsp;
				guard::ctor _1(print, "Tnamed");
				guard::ctor _2(print, "Ninst");
				cprint.printStructuredName(*decl, print) << fmt::nbsp;
				cprint.printTemplateParameters(*decl, print, true);
			} else
				nodecl();
		} else {
			if (auto decl = type->getDecl()) {
				guard::ctor _(print, "Tvar");
				cprint.printTypeName(*decl, print);
			} else {
				nodecl();
				if (false) {
					// Previously, we complained but kept going with the IST.
					cprint.printQualType(type->getInjectedSpecializationType(),
										 print, loc::of(type));
				}
			}
		}
	}

	void VisitMemberPointerType(const MemberPointerType* type,
								CoqPrinter& print, ClangPrinter& cprint) {
		print.ctor("Tmember_pointer");
		auto class_type = type->getClass();
		if (!print.templates()) {
			cprint.printTypeName(class_type->getAsCXXRecordDecl(), print,
								 loc::of(type));
		} else {
			/*
            `class_type` may not be a concrete class (e.g., it could
            be a template parameter).
            */
			this->Visit(class_type, print, cprint);
		}
		print.output() << fmt::nbsp;
		cprint.printQualType(type->getPointeeType(), print, loc::of(type));
		print.end_ctor();
	}

	void VisitMacroQualifiedType(const MacroQualifiedType* type,
								 CoqPrinter& print, ClangPrinter& cprint) {
		cprint.printQualType(type->getModifiedType(), print, loc::of(type));
	}

	void VisitUsingType(const UsingType* type, CoqPrinter& print,
						ClangPrinter& cprint) {
		assert(type->isSugared());
		cprint.printQualType(type->getUnderlyingType(), print, loc::of(type));
	}
};

PrintType PrintType::printer;

fmt::Formatter&
ClangPrinter::printType(const Type& type, CoqPrinter& print) {
	if (trace(Trace::Type))
		trace("printType", loc::of(type));
	__attribute__((unused)) auto depth = print.output().get_depth();
	PrintType::printer.Visit(&type, print, *this);
	assert(depth == print.output().get_depth());
	return print.output();
}

fmt::Formatter&
ClangPrinter::printType(const clang::Type* type, CoqPrinter& print,
						loc::loc loc) {
	if (type)
		return printType(*type, print);
	else
		fatal(print, *this, loc, "unexpected null type in printType");
}

fmt::Formatter&
ClangPrinter::printQualType(const QualType& qt, CoqPrinter& print,
							loc::loc loc) {
	if (trace(Trace::Type))
		trace("printQualType", loc::of(qt));
	if (auto p = qt.getTypePtrOrNull()) {
		if (qt.isLocalConstQualified()) {
			if (qt.isVolatileQualified()) {
				print.ctor("Qconst_volatile", false);
			} else {
				print.ctor("Qconst", false);
			}
			printType(*p, print);
			print.end_ctor();
		} else {
			if (qt.isLocalVolatileQualified()) {
				print.ctor("Qmut_volatile", false);
				printType(*p, print);
				print.end_ctor();
			} else {
				printType(*p, print);
			}
		}
		return print.output();
	} else
		fatal(print, *this, loc, "unexpected null type in printQualType");
}

fmt::Formatter&
ClangPrinter::printQualTypeOption(const QualType& qt, CoqPrinter& print,
								  loc::loc loc) {
	auto t = qt.getTypePtrOrNull();
	if (t == nullptr || t->isDependentType()) {
		return print.none();
	} else {
		print.some();
		printQualType(qt, print, loc);
		return print.end_ctor();
	}
}

fmt::Formatter&
ClangPrinter::printQualifier(const QualType& qt, CoqPrinter& print) const {
	return printQualifier(qt.isConstQualified(), qt.isVolatileQualified(),
						  print);
}

fmt::Formatter&
ClangPrinter::printQualifier(bool is_const, bool is_volatile,
							 CoqPrinter& print) const {
	if (is_const) {
		if (is_volatile) {
			return print.output() << "QCV";
		} else {
			return print.output() << "QC";
		}
	} else {
		if (is_volatile) {
			return print.output() << "QV";
		} else {
			return print.output() << "QM";
		}
	}
}
