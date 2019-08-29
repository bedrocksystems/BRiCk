#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Logging.hpp"
#include "TypeVisitorWithArgs.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>

using namespace clang;
using namespace fmt;

void
printQualType(const QualType& qt, CoqPrinter& print, ClangPrinter& cprint) {
    if (qt.isLocalConstQualified()) {
        if (qt.isVolatileQualified()) {
            print.ctor("Qconst_volatile", false);
        } else {
            print.ctor("Qconst", false);
        }
    } else {
        if (qt.isLocalVolatileQualified()) {
            print.ctor("Qmut_volatile", false);
        } else {
            print.ctor("Qmut", false);
        }
    }
    cprint.printType(qt.getTypePtr(), print);
    print.output() << fmt::rparen;
}

void
printQualifier(const QualType& qt, CoqPrinter& print) {
    print.begin_record();
    print.record_field("q_const");
    print.boolean(qt.isConstQualified());
    print.output() << ";" << fmt::nbsp;
    print.record_field("q_volatile");
    print.boolean(qt.isVolatileQualified());
    print.end_record();
}

const std::string
bitsize (unsigned n) {
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

class PrintType :
    public TypeVisitor<PrintType, void, CoqPrinter&, ClangPrinter&> {
private:
    PrintType() {}

public:
    static PrintType printer;

    void VisitType(const Type* type, CoqPrinter& print, ClangPrinter& cprint) {
        using namespace logging;
        fatal() << "[ERR] unsupported type: ";
        type->dump(fatal());
        fatal() << "\n";
        die();
    }

    void VisitDeducedType(const DeducedType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        cprint.printQualType(type->getDeducedType(), print);
    }

    void VisitTemplateTypeParmType(const TemplateTypeParmType* type,
                                   CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Ttemplate") << "\"" << type->getDecl()->getNameAsString()
                                << "\"" << fmt::rparen;
    }

    void VisitEnumType(const EnumType* type, CoqPrinter& print,
                       ClangPrinter& cprint) {
        print.ctor("Tref", false);
        cprint.printGlobalName(type->getDecl(), print);
        print.output() << fmt::rparen;
    }
    void VisitRecordType(const RecordType* type, CoqPrinter& print,
                         ClangPrinter& cprint) {
        print.ctor("Tref", false);
        cprint.printGlobalName(type->getDecl(), print);
        print.output() << fmt::rparen;
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
                print.output() << "T_int8";
                break;
            case 16:
                print.output() << "T_int16";
                break;
            case 32:
                print.output() << "T_int32";
                break;
            case 64:
                print.output() << "T_int64";
                break;
            case 128:
                print.output() << "T_int128";
                break;
            default:
                print.output() << "(Tint " << bitsize (sz) << " Signed)";
            }
        } else if (type->isUnsignedIntegerType()) {
            switch (auto sz = cprint.getTypeSize(type)) {
            case 8:
                print.output() << "T_uint8";
                break;
            case 16:
                print.output() << "T_uint16";
                break;
            case 32:
                print.output() << "T_uint32";
                break;
            case 64:
                print.output() << "T_uint64";
                break;
            case 128:
                print.output() << "T_uint128";
                break;
            default:
                print.output() << "(Tint " << bitsize (sz) << " Unsigned)";
            }
        }
    }

    void VisitBuiltinType(const BuiltinType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        // todo(gmm): record bitwidths from the context when they are defaulted.
        if (type->getKind() == BuiltinType::Kind::Bool) {
            print.output() << "Tbool";
        } else if (type->getKind() == BuiltinType::Kind::Int128) {
            print.output() << "T_int128";
        } else if (type->getKind() == BuiltinType::Kind::UInt128) {
            print.output() << "T_uint128";
        } else if (type->getKind() == BuiltinType::Kind::Int) {
            print.output() << "T_int";
        } else if (type->getKind() == BuiltinType::Kind::UInt) {
            print.output() << "T_uint";
        } else if (type->getKind() == BuiltinType::Kind::ULong) {
            print.output() << "T_ulong";
        } else if (type->getKind() == BuiltinType::Kind::UShort) {
            print.output() << "T_ushort";
        } else if (type->getKind() == BuiltinType::Kind::Long) {
            print.output() << "T_long";
        } else if (type->getKind() == BuiltinType::Kind::LongDouble) {
            print.output() << "T_long_double";
        } else if (type->getKind() == BuiltinType::Kind::LongLong) {
            print.output() << "T_longlong";
        } else if (type->getKind() == BuiltinType::Kind::ULongLong) {
            print.output() << "T_ulonglong";
        } else if (type->getKind() == BuiltinType::Kind::Short) {
            print.output() << "T_short";
        } else if (type->getKind() == BuiltinType::Kind::Char16) {
            print.output() << "T_char16";
        } else if (type->getKind() == BuiltinType::Kind::Char_S) {
            print.output() << "(Tchar " << bitsize (cprint.getTypeSize(type))
                           << "%N Signed)";
        } else if (type->getKind() == BuiltinType::Kind::SChar) {
            print.output() << "(Tchar " << bitsize (cprint.getTypeSize(type))
                           << "%N Signed)";
        } else if (type->getKind() == BuiltinType::Kind::UChar) {
            print.output() << "(Tchar " << bitsize (cprint.getTypeSize(type))
                           << "%N Unsigned)";
        } else if (type->getKind() == BuiltinType::Kind::Char_U) {
            print.output() << "(Tchar " << bitsize (cprint.getTypeSize(type))
                           << "%N Unsigned)";
        } else if (type->getKind() == BuiltinType::Kind::Char8) {
            print.output() << "T_char8";
        } else if (type->getKind() == BuiltinType::Kind::Char32) {
            print.output() << "T_char32";
        } else if (type->getKind() == BuiltinType::Kind::Void) {
            print.output() << "Tvoid";
        } else {
            using namespace logging;
            fatal() << "Unsupported type \""
                    << type->getNameAsCString(PrintingPolicy(LangOptions()))
                    << "\"\n";
            die();
        }
    }

    void VisitLValueReferenceType(const LValueReferenceType* type,
                                  CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Treference");
        printQualType(type->getPointeeType(), print, cprint);
        print.output() << fmt::rparen;
    }

    void VisitRValueReferenceType(const RValueReferenceType* type,
                                  CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Trv_reference");
        printQualType(type->getPointeeType(), print, cprint);
        print.output() << fmt::rparen;
    }

    void VisitPointerType(const PointerType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        print.ctor("Tpointer");
        printQualType(type->getPointeeType(), print, cprint);
        print.output() << fmt::rparen;
    }

    void VisitTypedefType(const TypedefType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        print.ctor("@Talias");
        cprint.printQualType(
            type->getDecl()->getCanonicalDecl()->getUnderlyingType(), print);
        print.output() << fmt::nbsp;
        cprint.printGlobalName(type->getDecl(), print);
        print.output() << fmt::rparen;
    }

    void VisitFunctionProtoType(const FunctionProtoType* type,
                                CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Tfunction");
        printQualType(type->getReturnType(), print, cprint);
        print.output() << fmt::nbsp;
        print.begin_list();
        for (auto i : type->param_types()) {
            printQualType(i, print, cprint);
            print.cons();
        }
        print.end_list();

        print.output() << fmt::rparen;
    }

    void VisitElaboratedType(const ElaboratedType* type, CoqPrinter& print,
                             ClangPrinter& cprint) {
        printQualType(type->getNamedType(), print, cprint);
    }

    void VisitConstantArrayType(const ConstantArrayType* type,
                                CoqPrinter& print, ClangPrinter& cprint) {
        print.ctor("Tarray");
        printQualType(type->getElementType(), print, cprint);
        print.output() << fmt::nbsp << type->getSize().getLimitedValue()
                       << fmt::rparen;
    }

    void VisitSubstTemplateTypeParmType(const SubstTemplateTypeParmType* type,
                                        CoqPrinter& print,
                                        ClangPrinter& cprint) {
        printQualType(type->getReplacementType(), print, cprint);
    }

    void VisitIncompleteArrayType(const IncompleteArrayType* type,
                                  CoqPrinter& print, ClangPrinter& cprint) {
        // note(gmm): i might want to note the sugar.
        print.ctor("Qconst");
        print.ctor("Tpointer", false);
        printQualType(type->getElementType(), print, cprint);
        print.output() << fmt::rparen << fmt::rparen;
    }

    void VisitDecayedType(const DecayedType* type, CoqPrinter& print,
                          ClangPrinter& cprint) {
        print.ctor("Qconst");
        print.ctor("Tpointer", false);
        printQualType(type->getPointeeType(), print, cprint);
        print.output() << fmt::rparen << fmt::rparen;
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

    void VisitInjectedClassNameType(const InjectedClassNameType* type,
                                    CoqPrinter& print, ClangPrinter& cprint) {
        if (type->getDecl()) {
            print.ctor("Tref");
            cprint.printGlobalName(type->getDecl(), print);
            print.end_ctor();
        } else {
            logging::log() << "no underlying declaration for \n";
            type->dump(logging::log());
            cprint.printQualType(type->getInjectedSpecializationType(), print);
        }
    }
};

PrintType PrintType::printer;

void
ClangPrinter::printType(const clang::Type* type, CoqPrinter& print) {
    auto depth = print.output().get_depth();
    PrintType::printer.Visit(type, print, *this);
    assert(depth == print.output().get_depth());
}

void
ClangPrinter::printQualType(const QualType& qt, CoqPrinter& print) {
    auto depth = print.output().get_depth();
    ::printQualType(qt, print, *this);
    assert(depth == print.output().get_depth());
}

void
ClangPrinter::printQualifier(const QualType& qt, CoqPrinter& print) const {
    auto depth = print.output().get_depth();
    ::printQualifier(qt, print);
    assert(depth == print.output().get_depth());
}

void
ClangPrinter::printQualifier(bool is_const, bool is_volatile,
                             CoqPrinter& print) const {
    print.begin_record();
    print.record_field("q_const");
    print.boolean(is_const);
    print.output() << ";" << fmt::nbsp;
    print.record_field("q_volatile");
    print.boolean(is_volatile);
    print.end_record();
}
