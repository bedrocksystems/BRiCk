/*
 * Copyright (c) 2020 BedRock Systems, Inc.
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
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>

using namespace clang;
using namespace fmt;

const std::string
bitsize(unsigned n) {
    switch (n) {
    case 8:
        return "W8";
    case 16:
        return "W16";
    case 32:
        return "W32";
    case 64:
        return "W64";
    case 128:
        return "W128";
    default:
        return "unknown_bit_size";
    }
}

static void
unsupported_type(const Type* type, CoqPrinter& print, ClangPrinter& cprint) {
    print.ctor("Tunsupported", false);
    print.str(type->getTypeClassName());
    print.end_ctor();

    using namespace logging;
    unsupported() << "[WARN] unsupported type (" << type->getTypeClassName()
                  << "):";
#if CLANG_VERSION_MAJOR >= 11
    type->dump(unsupported(), cprint.getContext());
#else
    type->dump(unsupported());
#endif

    unsupported() << "\n";
}

class PrintType :
    public TypeVisitor<PrintType, void, CoqPrinter&, ClangPrinter&> {
private:
    PrintType() {}

public:
    static PrintType printer;

    void VisitType(const Type* type, CoqPrinter& print, ClangPrinter& cprint) {
        unsupported_type(type, print, cprint);
    }

    void VisitAttributedType(const AttributedType* type, CoqPrinter& print,
                             ClangPrinter& cprint) {
        cprint.printQualType(type->getModifiedType(), print);
    }

    void VisitUnaryTransformType(const UnaryTransformType* type,
                                 CoqPrinter& print, ClangPrinter& cprint) {

        switch (type->getUTTKind()) {

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

            // The enumeration
            cprint.printQualType(type->getBaseType(), print);
            print.output() << fmt::nbsp;

            // The underlying type
            cprint.printQualType(type->getUnderlyingType(), print);
            print.end_ctor();

            break;

        default:
            unsupported_type(type, print, cprint);
            break;
        }
    }

    void VisitDeducedType(const DeducedType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        if (type->isDeduced()) {
            cprint.printQualType(type->getDeducedType(), print);
        } else {
            unsupported_type(type, print, cprint);
        }
    }

    void VisitTemplateTypeParmType(const TemplateTypeParmType* type,
                                   CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Tvar");
        print.str(type->getDecl()->getNameAsString());
        print.end_ctor();
    }

    void VisitEnumType(const EnumType* type, CoqPrinter& print,
                       ClangPrinter& cprint) {
        auto ed = type->getDecl()->getCanonicalDecl();
        print.ctor("Tenum", false);
        cprint.printTypeName(ed, print);
        print.end_ctor();
    }

    void VisitRecordType(const RecordType* type, CoqPrinter& print,
                         ClangPrinter& cprint) {
        print.ctor("Tnamed", false);
        cprint.printTypeName(type->getDecl(), print);
        print.end_ctor();
    }

    void VisitParenType(const ParenType* type, CoqPrinter& print,
                        ClangPrinter& cprint) {
        cprint.printQualType(type->getInnerType(), print);
    }

    void printTypeSugar(const BuiltinType* type, CoqPrinter& print,
                        ClangPrinter& cprint) {
        if (type->isSignedIntegerType()) {
            switch (auto sz = cprint.getTypeSize(type)) {
            case 8:
                print.output() << "Ti8";
                break;
            case 16:
                print.output() << "Ti16";
                break;
            case 32:
                print.output() << "Ti32";
                break;
            case 64:
                print.output() << "Ti64";
                break;
            case 128:
                print.output() << "Ti128";
                break;
            default:
                print.output() << "(Tnum " << bitsize(sz) << " Signed)";
            }
        } else if (type->isUnsignedIntegerType()) {
            switch (auto sz = cprint.getTypeSize(type)) {
            case 8:
                print.output() << "Tu8";
                break;
            case 16:
                print.output() << "Tu16";
                break;
            case 32:
                print.output() << "Tu32";
                break;
            case 64:
                print.output() << "Tu64";
                break;
            case 128:
                print.output() << "Tu128";
                break;
            default:
                print.output() << "(Tnum " << bitsize(sz) << " Unsigned)";
            }
        }
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
#if CLANG_VERSION_MAJOR == 10
        case BuiltinType::Kind::SveInt8:
        case BuiltinType::Kind::SveInt16:
        case BuiltinType::Kind::SveInt32:
        case BuiltinType::Kind::SveInt64:
        case BuiltinType::Kind::SveUint8:
        case BuiltinType::Kind::SveUint16:
        case BuiltinType::Kind::SveUint32:
        case BuiltinType::Kind::SveUint64:
        case BuiltinType::Kind::SveFloat16:
        case BuiltinType::Kind::SveFloat32:
        case BuiltinType::Kind::SveFloat64:
        case BuiltinType::Kind::SveBool:
            print.output() << fmt::lparen << "Tarch None \""
                           << type->getNameAsCString(
                                  PrintingPolicy(LangOptions()))
                           << "\"" << fmt::rparen;
            break;
#endif
        case BuiltinType::Kind::Dependent:
            if (!print.templates()) {
                unsupported_type(type, print, cprint);
                using namespace logging;
                fatal()
                    << "Clang failed to resolve type, due to earlier errors or "
                       "unresolved templates\n"
                    << "Try fixing earlier errors, or ask for help. Aborting\n";
                die();
                break;
            }
            [[fallthrough]];

        default:
            if (type->isAnyCharacterType()) {
                assert(false && "unexpected character type");
            } else if (type->isFloatingPoint()) {
                assert(false && "unexpected floating point type");
            } else if (type->isIntegerType()) {
                assert(false);
#if CLANG_VERSION_MAJOR >= 11
            } else if (type->isSizelessBuiltinType()) {
                print.output() << fmt::lparen << "Tarch None \""
                               << type->getNameAsCString(
                                      cprint.getContext().getPrintingPolicy())
                               << "\"" << fmt::rparen;
                break;
#endif
            } else if (print.templates() && type->isDependentType()) {
                print.output() << "Tdependent";
            } else {
                unsupported_type(type, print, cprint);
            }
        }
    }

    void VisitLValueReferenceType(const LValueReferenceType* type,
                                  CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Tref", false);
        cprint.printQualType(type->getPointeeType(), print);
        print.end_ctor();
    }

    void VisitRValueReferenceType(const RValueReferenceType* type,
                                  CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Trv_ref", false);
        cprint.printQualType(type->getPointeeType(), print);
        print.end_ctor();
    }

    void VisitPointerType(const PointerType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        print.ctor("Tptr", false);
        cprint.printQualType(type->getPointeeType(), print);
        print.end_ctor();
    }

    void VisitTypedefType(const TypedefType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        if (PRINT_ALIAS) {
            print.ctor("@Talias", false);
            print.type() << fmt::nbsp;
            print.output() << "\"";
            cprint.printTypeName(type->getDecl(), print);
            // printing a "human readable" type
            // type->getDecl()->printQualifiedName(print.output().nobreak());
            print.output() << "\"" << fmt::nbsp;
            cprint.printQualType(
                type->getDecl()->getCanonicalDecl()->getUnderlyingType(),
                print);
            print.end_ctor();
        } else {
            cprint.printQualType(
                type->getDecl()->getCanonicalDecl()->getUnderlyingType(),
                print);
        }
    }

    void VisitFunctionProtoType(const FunctionProtoType* type,
                                CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("@Tfunction");
        cprint.printCallingConv(type->getCallConv(), print);
        print.output() << fmt::nbsp;
        cprint.printVariadic(type->isVariadic(), print);
        print.output() << fmt::nbsp;
        cprint.printQualType(type->getReturnType(), print);
        print.output() << fmt::nbsp;
        print.list(type->param_types(),
                   [&](auto print, auto i) { cprint.printQualType(i, print); });
        print.end_ctor();
    }

    void VisitElaboratedType(const ElaboratedType* type, CoqPrinter& print,
                             ClangPrinter& cprint) {
        cprint.printQualType(type->getNamedType(), print);
    }

    void VisitConstantArrayType(const ConstantArrayType* type,
                                CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Tarray");
        cprint.printQualType(type->getElementType(), print);
        print.output() << fmt::nbsp << type->getSize().getLimitedValue();
        print.end_ctor();
    }

    void VisitSubstTemplateTypeParmType(const SubstTemplateTypeParmType* type,
                                        CoqPrinter& print,
                                        ClangPrinter& cprint) {
        cprint.printQualType(type->getReplacementType(), print);
    }

    void VisitIncompleteArrayType(const IncompleteArrayType* type,
                                  CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Tincomplete_array");
        cprint.printQualType(type->getElementType(), print);
        print.end_ctor();
    }

    void VisitVariableArrayType(const VariableArrayType* type,
                                CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Tvariable_array");
        cprint.printQualType(type->getElementType(), print);
        print.output() << fmt::nbsp;
        cprint.printExpr(type->getSizeExpr(), print);
        print.end_ctor();
    }

    void VisitDecayedType(const DecayedType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        print.ctor("Tdecay_type");
        cprint.printQualType(type->getOriginalType(), print);
        print.output() << fmt::nbsp;
        cprint.printQualType(type->getAdjustedType(), print);
        print.end_ctor();
    }

    void VisitTemplateSpecializationType(const TemplateSpecializationType* type,
                                         CoqPrinter& print,
                                         ClangPrinter& cprint) {
        if (type->isSugared()) {
            cprint.printQualType(type->desugar(), print);
        } else {
            unsupported_type(type, print, cprint);
        }
    }

    void VisitDecltypeType(const DecltypeType* type, CoqPrinter& print,
                           ClangPrinter& cprint) {
        if (type->isSugared()) {
            // The guard ensure the type visitor terminates.
            cprint.printQualType(type->desugar(), print);
        } else if (print.templates()) {
            cprint.printQualType(type->getUnderlyingType(), print);
        } else {
            unsupported_type(type, print, cprint);
        }
    }

    void VisitTypeOfExprType(const TypeOfExprType* type, CoqPrinter& print,
                             ClangPrinter& cprint) {
        if (type->isSugared()) {
            // The guard ensure the type visitor terminates.
            cprint.printQualType(type->desugar(), print);
        } else if (print.templates()) {
            /*
            TODO: Test whether we need printQualTypeOption here.
            */
            cprint.printQualType(type->getUnderlyingExpr()->getType(), print);
        } else {
            unsupported_type(type, print, cprint);
        }
    }

    void VisitInjectedClassNameType(const InjectedClassNameType* type,
                                    CoqPrinter& print, ClangPrinter& cprint) {
        if (type->getDecl()) {
            print.ctor("Tnamed", false);
            cprint.printTypeName(type->getDecl(), print);
            print.end_ctor();
        } else {
            logging::log() << "no underlying declaration for \n";
#if CLANG_VERSION_MAJOR >= 11
            type->dump(logging::log(), cprint.getContext());
#else
            type->dump(logging::log());
#endif
            cprint.printQualType(type->getInjectedSpecializationType(), print);
        }
    }

    void VisitMemberPointerType(const MemberPointerType* type,
                                CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Tmember_pointer");
        auto class_type = type->getClass();
        if (!print.templates()) {
            cprint.printTypeName(class_type->getAsCXXRecordDecl(), print);
        } else {
            /*
            `class_type` may not be a concrete class (e.g., it could
            be a template parameter).
            */
            this->Visit(class_type, print, cprint);
        }
        print.output() << fmt::nbsp;
        cprint.printQualType(type->getPointeeType(), print);
        print.end_ctor();
    }

    void VisitMacroQualifiedType(const MacroQualifiedType* type,
                                 CoqPrinter& print, ClangPrinter& cprint) {
        cprint.printQualType(type->getModifiedType(), print);
    }

#if CLANG_VERSION_MAJOR >= 14
    void VisitUsingType(const UsingType* type, CoqPrinter& print,
                        ClangPrinter& cprint) {
        assert(type->isSugared());
        cprint.printQualType(type->getUnderlyingType(), print);
    }
#endif
};

PrintType PrintType::printer;

void
ClangPrinter::printType(const clang::Type* type, CoqPrinter& print) {
    __attribute__((unused)) auto depth = print.output().get_depth();
    PrintType::printer.Visit(type, print, *this);
    assert(depth == print.output().get_depth());
}

void
ClangPrinter::printQualType(const QualType& qt, CoqPrinter& print) {
    if (auto p = qt.getTypePtrOrNull()) {
        if (qt.isLocalConstQualified()) {
            if (qt.isVolatileQualified()) {
                print.ctor("Qconst_volatile", false);
            } else {
                print.ctor("Qconst", false);
            }
            printType(p, print);
            print.end_ctor();
        } else {
            if (qt.isLocalVolatileQualified()) {
                print.ctor("Qmut_volatile", false);
                printType(p, print);
                print.end_ctor();
            } else {
                printType(p, print);
            }
        }
    } else {
        using namespace logging;
        fatal() << "unexpected null type in printQualType\n";
        die();
    }
}

void
ClangPrinter::printQualTypeOption(const QualType& qt, CoqPrinter& print) {
    auto t = qt.getTypePtrOrNull();
    if (t == nullptr || t->isDependentType()) {
        print.none();
    } else {
        print.some();
        printQualType(qt, print);
        print.end_ctor();
    }
}

void
ClangPrinter::printQualifier(const QualType& qt, CoqPrinter& print) const {
    printQualifier(qt.isConstQualified(), qt.isVolatileQualified(), print);
}

void
ClangPrinter::printQualifier(bool is_const, bool is_volatile,
                             CoqPrinter& print) const {
    if (is_const) {
        if (is_volatile) {
            print.output() << "QCV";
        } else {
            print.output() << "QC";
        }
    } else {
        if (is_volatile) {
            print.output() << "QV";
        } else {
            print.output() << "QM";
        }
    }
}
