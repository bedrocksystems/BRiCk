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
        print.ctor("Ttemplate")
            << "\"" << type->getDecl()->getNameAsString() << "\"";
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
        case BuiltinType::Kind::Bool:
            print.output() << "Tbool";
            break;
        case BuiltinType::Kind::Void:
            print.output() << "Tvoid";
            break;
        case BuiltinType::Kind::NullPtr:
            print.output() << "Tnullptr";
            break;
        case BuiltinType::Kind::Dependent:
            print.output() << "Tunsupported \"type-dependent type\"";
            using namespace logging;
            fatal() << "Clang failed to resolve type, due to earlier errors or "
                       "unresolved templates\n"
                    << "Try fixing earlier errors, or ask for help. Aborting\n";
            die();

            break;
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
        default:
            if (type->isAnyCharacterType()) {
                print.output()
                    << "(Tchar " << bitsize(cprint.getTypeSize(type)) << " "
                    << (type->isSignedInteger() ? "Signed" : "Unsigned") << ")";
            } else if (type->isFloatingPoint()) {
                print.output()
                    << "(Tfloat " << bitsize(cprint.getTypeSize(type)) << ")";
            } else if (type->isIntegerType()) {
                print.output()
                    << "(Tnum " << bitsize(cprint.getTypeSize(type)) << " "
                    << (type->isSignedInteger() ? "Signed" : "Unsigned") << ")";
#if CLANG_VERSION_MAJOR >= 11
            } else if (type->isSizelessBuiltinType()) {
                print.output() << fmt::lparen << "Tarch None \""
                               << type->getNameAsCString(
                                      cprint.getContext().getPrintingPolicy())
                               << "\"" << fmt::rparen;
                break;
#endif
            } else {
                using namespace logging;
                fatal() << "[ERR] Unsupported builtin type (" << type->getKind()
                        << "): \""
                        << type->getNameAsCString(
                               cprint.getContext().getPrintingPolicy())
                        << "\"\n";
                die();
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
            print.ctor("@Talias", false) << "\"";
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
        cprint.printQualType(type->getPointeeType(), print);
        print.end_ctor();
    }

    void VisitTemplateSpecializationType(const TemplateSpecializationType* type,
                                         CoqPrinter& print,
                                         ClangPrinter& cprint) {
        if (type->isSugared()) {
            cprint.printQualType(type->desugar(), print);
        } else {
            VisitType(type, print, cprint);
        }
    }

    void VisitDecltypeType(const DecltypeType* type, CoqPrinter& print,
                           ClangPrinter& cprint) {
        cprint.printQualType(type->desugar(), print);
    }

    void VisitTypeOfExprType(const TypeOfExprType* type, CoqPrinter& print,
                             ClangPrinter& cprint) {
        cprint.printQualType(type->desugar(), print);
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
        cprint.printTypeName(type->getClass()->getAsCXXRecordDecl(), print);
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
