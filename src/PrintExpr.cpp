/*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/Version.inc"

using namespace clang;
using namespace fmt;

// todo(gmm): this is duplicated!
bool
is_builtin(const Decl* d) {
    if (const FunctionDecl* fd = dyn_cast_or_null<const FunctionDecl>(d)) {
        if (Builtin::ID::NotBuiltin != fd->getBuiltinID()) {
            return true;
        }
    }
    return false;
}

void
printCastKind(Formatter& out, const CastKind ck) {
    if (ck == CastKind::CK_LValueToRValue) {
        out << "Cl2r";
    } else if (ck == CastKind::CK_Dependent) {
        out << "Cdependent";
    } else if (ck == CastKind::CK_FunctionToPointerDecay) {
        out << "Cfunction2pointer";
    } else if (ck == CastKind::CK_NoOp) {
        out << "Cnoop";
    } else if (ck == CastKind::CK_BitCast) {
        out << "Cbitcast";
    } else if (ck == CastKind::CK_IntegralCast) {
        out << "Cintegral";
    } else if (ck == CastKind::CK_IntegralToBoolean) {
        out << "Cint2bool";
    } else if (ck == CastKind::CK_PointerToBoolean) {
        out << "Cptr2bool";
    } else if (ck == CastKind::CK_PointerToIntegral) {
        out << "Cpointer2int";
    } else if (ck == CastKind::CK_IntegralToPointer) {
        out << "Cint2pointer";
    } else if (ck == CastKind::CK_ArrayToPointerDecay) {
        out << "Carray2pointer";
    } else if (ck == CastKind::CK_ConstructorConversion) {
        out << "Cconstructorconversion";
    } else if (ck == CastKind::CK_BuiltinFnToFnPtr) {
        out << "Cbuiltin2function";
    } else if (ck == CastKind::CK_NullToPointer) {
        out << "Cnull2ptr";
    } else if (ck == CastKind::CK_DerivedToBase ||
               ck == CastKind::CK_UncheckedDerivedToBase) {
        out << "Cderived2base";
    } else if (ck == CastKind::CK_BaseToDerived) {
        out << "Cbase2derived";
    } else if (ck == CastKind::CK_ToVoid) {
        out << "C2void";
    } else {
#if CLANG_VERSION_MAJOR >= 7
        logging::unsupported() << "unsupported cast kind \""
                               << CastExpr::getCastKindName(ck) << "\"\n";
#else
        logging::unsupported() << "unsupported cast kind ..." << ck << "\n";
#endif
        out << "Cunsupported";
    }
}

class PrintExpr :
    public ConstStmtVisitor<PrintExpr, void, CoqPrinter&, ClangPrinter&,
                            const ASTContext&> {
private:
    void done(const Expr* expr, CoqPrinter& print, ClangPrinter& cprint) {
        print.output() << fmt::nbsp;
        cprint.printQualType(expr->getType(), print);
        print.end_ctor();
    }

#if CLANG_VERSION_MAJOR >= 9
    void printOptionalExpr(Optional<const Expr*> expr, CoqPrinter& print,
                           ClangPrinter& cprint) {
        if (expr.hasValue()) {
            print.ctor("Some");
            cprint.printExpr(expr.getValue(), print);
            print.end_ctor();
        } else {
            print.none();
        }
    }
#else
    void printOptionalExpr(const Expr* expr, CoqPrinter& print,
                           ClangPrinter& cprint) {
        if (expr != nullptr) {
            print.ctor("Some");
            cprint.printExpr(expr, print);
            print.end_ctor();
        } else {
            print.none();
        }
    }
#endif

public:
    static PrintExpr printer;

    void VisitStmt(const Stmt* stmt, CoqPrinter& print, ClangPrinter& cprint,
                   const ASTContext&) {
        logging::fatal() << "while printing an expr, got a statement '"
                         << stmt->getStmtClassName() << " at "
                         << cprint.sourceRange(stmt->getSourceRange()) << "'\n";
        logging::die();
    }

    void VisitExpr(const Expr* expr, CoqPrinter& print, ClangPrinter& cprint,
                   const ASTContext& ctxt) {
        using namespace logging;
        unsupported() << "unrecognized expression '" << expr->getStmtClassName()
                      << "' at " << cprint.sourceRange(expr->getSourceRange())
                      << "\n";
        print.ctor("Eunsupported");
        print.str(expr->getStmtClassName());
        done(expr, print, cprint);
    }

    void printBinaryOperator(BinaryOperator::Opcode op, StringRef def,
                             CoqPrinter& print, const ASTContext& ctxt) {
        switch (op) {
#define CASE(k, s)                                                             \
    case BinaryOperatorKind::BO_##k:                                           \
        print.output() << s;                                                   \
        break;
            CASE(Add, "Badd")
            CASE(And, "Band")
            CASE(Cmp, "Bcmp")
            CASE(Div, "Bdiv")
            CASE(EQ, "Beq")
            CASE(GE, "Bge")
            CASE(GT, "Bgt")
            CASE(LE, "Ble")
            CASE(LT, "Blt")
            CASE(Mul, "Bmul")
            CASE(NE, "Bneq")
            CASE(Or, "Bor")
            CASE(Rem, "Bmod")
            CASE(Shl, "Bshl")
            CASE(Shr, "Bshr")
            CASE(Sub, "Bsub")
            CASE(Xor, "Bxor")
            CASE(PtrMemD, "Bdotp")
            CASE(PtrMemI, "Bdotip")
#undef CASE
        default:
            logging::unsupported() << "defaulting binary operator\n";
            print.ctor("Bother") << "\"" << def << "\"" << fmt::rparen;
            break;
        }
    }

    void VisitBinaryOperator(const BinaryOperator* expr, CoqPrinter& print,
                             ClangPrinter& cprint, const ASTContext& ctxt) {
#define ACASE(k, v)                                                            \
    case BinaryOperatorKind::BO_##k##Assign:                                   \
        print.ctor("Eassign_op") << #v << fmt::nbsp;                           \
        break;
        switch (expr->getOpcode()) {
        case BinaryOperatorKind::BO_Comma:
            print.ctor("Ecomma");
            cprint.printValCat(expr->getLHS(), print);
            print.output() << fmt::nbsp;
            break;
        case BinaryOperatorKind::BO_LAnd:
            print.ctor("Eseqand");
            break;
        case BinaryOperatorKind::BO_LOr:
            print.ctor("Eseqor");
            break;
        case BinaryOperatorKind::BO_Assign:
            print.ctor("Eassign");
            break;
            ACASE(Add, Badd)
            ACASE(And, Band)
            ACASE(Div, Bdiv)
            ACASE(Mul, Bmul)
            ACASE(Or, Bor)
            ACASE(Rem, Bmod)
            ACASE(Shl, Bshl)
            ACASE(Shr, Bshr)
            ACASE(Sub, Bsub)
            ACASE(Xor, Bxor)
        default:
            print.ctor("Ebinop");
            printBinaryOperator(expr->getOpcode(), expr->getOpcodeStr(), print,
                                ctxt);
            print.output() << fmt::nbsp;
            break;
        }
#undef ACASE
        cprint.printExpr(expr->getLHS(), print);
        print.output() << fmt::nbsp;
        cprint.printExpr(expr->getRHS(), print);
        done(expr, print, cprint);
    }

    void VisitDependentScopeDeclRefExpr(const DependentScopeDeclRefExpr* expr,
                                        CoqPrinter& print, ClangPrinter& cprint,
                                        const ASTContext& ctxt) {
        ConstStmtVisitor<
            PrintExpr, void, CoqPrinter&, ClangPrinter&,
            const ASTContext&>::VisitDependentScopeDeclRefExpr(expr, print,
                                                               cprint, ctxt);
    }

    void printUnaryOperator(UnaryOperator::Opcode op, CoqPrinter& print) {
        switch (op) {
#define CASE(k, s)                                                             \
    case UnaryOperatorKind::UO_##k:                                            \
        print.output() << s;                                                   \
        break;
            CASE(Minus, "Uminus")
            CASE(Not, "Ubnot")
            CASE(LNot, "Unot")
            CASE(PostDec, "<PostDec>")
            CASE(PostInc, "<PostInc>")
            CASE(PreDec, "<PreDec>")
            CASE(PreInc, "<PreInc>")
#undef CASE
        default:
            logging::unsupported() << "unsupported unary operator\n";
            print.output() << "(Uother \"" << UnaryOperator::getOpcodeStr(op)
                           << "\")";
            break;
        }
    }

    void VisitUnaryOperator(const UnaryOperator* expr, CoqPrinter& print,
                            ClangPrinter& cprint, const ASTContext&) {
        switch (expr->getOpcode()) {
        case UnaryOperatorKind::UO_AddrOf:
            print.ctor("Eaddrof");
            break;
        case UnaryOperatorKind::UO_Deref:
            print.ctor("Ederef");
            break;
        case UnaryOperatorKind::UO_PostInc:
            print.ctor("Epostinc");
            break;
        case UnaryOperatorKind::UO_PreInc:
            print.ctor("Epreinc");
            break;
        case UnaryOperatorKind::UO_PostDec:
            print.ctor("Epostdec");
            break;
        case UnaryOperatorKind::UO_PreDec:
            print.ctor("Epredec");
            break;
        default:
            print.ctor("Eunop");
            printUnaryOperator(expr->getOpcode(), print);
            print.output() << fmt::nbsp;
        }
        cprint.printExpr(expr->getSubExpr(), print);
        done(expr, print, cprint);
    }

    void VisitDeclRefExpr(const DeclRefExpr* expr, CoqPrinter& print,
                          ClangPrinter& cprint, const ASTContext& ctxt) {
        auto d = expr->getDecl();
        if (isa<EnumConstantDecl>(d)) {
            print.ctor("Econst_ref", false);
        } else {
            print.ctor("Evar", false);
        }
        cprint.printName(d, print);
        done(expr, print, cprint);
    }

    void VisitCallExpr(const CallExpr* expr, CoqPrinter& print,
                       ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Ecall");
        cprint.printExpr(expr->getCallee(), print);
        print.output() << fmt::line;
        print.begin_list();
        for (auto i : expr->arguments()) {
            cprint.printExprAndValCat(i, print);
            print.cons();
        }
        print.end_list();
        done(expr, print, cprint);
    }

    void VisitCastExpr(const CastExpr* expr, CoqPrinter& print,
                       ClangPrinter& cprint, const ASTContext&) {
        if (expr->getCastKind() == CastKind::CK_ConstructorConversion) {
            // note: the Clang AST records a "FunctionalCastExpr" with a constructor
            // but the child node of this is the constructor!
            cprint.printExpr(expr->getSubExpr(), print);
        } else if (auto cf = expr->getConversionFunction()) {
            // desugar user casts to function calls
            print.ctor("Ecast");
            print.ctor("Cuser");
            cprint.printGlobalName(cf, print);
            print.end_ctor();

            cprint.printExprAndValCat(expr->getSubExpr(), print);
            done(expr, print, cprint);

        } else {
            print.ctor("Ecast");
            print.ctor("CCcast", false);
            printCastKind(print.output(), expr->getCastKind());
            print.end_ctor();

            print.output() << fmt::nbsp;
            cprint.printExprAndValCat(expr->getSubExpr(), print);
            done(expr, print, cprint);
        }
    }

    void VisitImplicitCastExpr(const ImplicitCastExpr* expr, CoqPrinter& print,
                               ClangPrinter& cprint, const ASTContext& ctxt) {
        // todo(gmm): this is a complete hack because there is no way that i know of
        // to get the type of a builtin. what this does is get the type of the expression
        // that contains the builtin.
        if (auto ref = dyn_cast<DeclRefExpr>(expr->getSubExpr())) {
            if (is_builtin(ref->getDecl())) {
                // assume that this is a builtin
                print.ctor("Evar", false);
                print.ctor("Gname", false);
                cprint.printGlobalName(ref->getDecl(), print);
                print.end_ctor();
                done(expr, print, cprint);
                return;
            }
        }
        VisitCastExpr(expr, print, cprint, ctxt);
    }

    void VisitCXXNamedCastExpr(const CXXNamedCastExpr* expr, CoqPrinter& print,
                               ClangPrinter& cprint, const ASTContext& ctxt) {
        if (expr->getConversionFunction()) {
            return VisitCastExpr(expr, print, cprint, ctxt);
        }

        print.ctor("Ecast");
        if (isa<CXXReinterpretCastExpr>(expr)) {
            print.ctor("Creinterpret", false);
            cprint.printQualType(expr->getType(), print);
            print.end_ctor();
        } else if (isa<CXXConstCastExpr>(expr)) {
            print.ctor("Cconst", false);
            cprint.printQualType(expr->getType(), print);
            print.end_ctor();
        } else if (isa<CXXStaticCastExpr>(expr)) {
            auto from = expr->getSubExpr()
                            ->getType()
                            .getTypePtr()
                            ->getPointeeCXXRecordDecl();
            auto to = expr->getType().getTypePtr()->getPointeeCXXRecordDecl();
            if (from && to) {
                print.ctor("Cstatic", false);
                cprint.printGlobalName(from, print);
                print.output() << fmt::nbsp;
                cprint.printGlobalName(to, print);
                print.end_ctor();
            } else {
                print.ctor("CCcast", false);
                printCastKind(print.output(), expr->getCastKind());
                print.end_ctor();
            }
        } else if (isa<CXXDynamicCastExpr>(expr)) {
            using namespace logging;
            fatal() << "dynamic casts are not supported (at "
                    << expr->getSourceRange().printToString(
                           ctxt.getSourceManager())
                    << ")\n";
            die();
        } else {
            using namespace logging;
            fatal() << "unknown named cast" << expr->getCastKindName()
                    << " (at "
                    << expr->getSourceRange().printToString(
                           ctxt.getSourceManager())
                    << ")\n";
            die();
        }
        print.output() << fmt::nbsp;

        cprint.printExprAndValCat(expr->getSubExpr(), print);
        done(expr, print, cprint);
    }

    void VisitIntegerLiteral(const IntegerLiteral* lit, CoqPrinter& print,
                             ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Eint", false);
        if (lit->getType()->isSignedIntegerOrEnumerationType()) {
            print.output() << lit->getValue().toString(10, true) << "%Z";
        } else {
            print.output() << lit->getValue().toString(10, false);
        }
        done(lit, print, cprint);
    }

    void VisitCharacterLiteral(const CharacterLiteral* lit, CoqPrinter& print,
                               ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Echar", false) << lit->getValue() << "%Z";
        done(lit, print, cprint);
    }

    void VisitStringLiteral(const StringLiteral* lit, CoqPrinter& print,
                            ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Estring", false);
        for (auto i = lit->getBytes().begin(), end = lit->getBytes().end();
             i != end; ++i) {
            char buf[25];
            sprintf(buf, "Byte.x%02x", (unsigned)*i);
            print.output() << "(BS.String " << buf << " ";
        }
        print.output() << "BS.EmptyString";
        for (auto i = lit->getBytes().begin(), end = lit->getBytes().end();
             i != end; ++i) {
            print.output() << ")";
        }
        done(lit, print, cprint);
    }

    void VisitCXXBoolLiteralExpr(const CXXBoolLiteralExpr* lit,
                                 CoqPrinter& print, ClangPrinter& cprint,
                                 const ASTContext&) {
        if (lit->getValue()) {
            print.output() << "(Ebool true)";
        } else {
            print.output() << "(Ebool false)";
        }
    }

    void VisitMemberExpr(const MemberExpr* expr, CoqPrinter& print,
                         ClangPrinter& cprint, const ASTContext&) {
        /* TCB: semantics of accesses to static members.
        When `m` is a static member of `T` and `e : T`,
        we desugar `e->member` to `e, T::member`.
        */
        if (auto vd = dyn_cast<VarDecl>(expr->getMemberDecl())) {
            if (vd->isStaticDataMember()) {
                print.ctor("Ecomma");
                cprint.printValCat(expr->getBase(), print);
                print.output() << fmt::nbsp;
                cprint.printExpr(expr->getBase(), print);
                print.output() << fmt::nbsp;
                print.ctor("Evar", false);
                cprint.printName(vd, print);
                print.output() << fmt::nbsp;
                cprint.printQualType(vd->getType(), print);
                print.end_ctor();
                done(expr, print, cprint);

#if 0
                // this handles the special case of static members
                print.ctor("Evar");
                cprint.printName(vd, print);
                done(expr, print, cprint);
#endif
                return;
            }
        } else if (auto md = dyn_cast<CXXMethodDecl>(expr->getMemberDecl())) {
            if (md->isStatic()) {
                print.ctor("Ecomma");
                cprint.printValCat(expr->getBase(), print);
                print.output() << fmt::nbsp;
                cprint.printExpr(expr->getBase(), print);
                print.output() << fmt::nbsp;
                print.ctor("Evar", false);
                cprint.printName(md, print);
                print.output() << fmt::nbsp;
                cprint.printQualType(md->getType(), print);
                print.end_ctor();
                done(expr, print, cprint);
                return;
            }
        }
        print.ctor("Emember");

        auto base = expr->getBase();
        if (expr->isArrow()) {
            print.output() << "Lvalue" << fmt::nbsp;
            print.ctor("Ederef");
            cprint.printExpr(base, print);
            print.output() << fmt::nbsp;
            cprint.printQualType(base->getType()->getPointeeType(), print);
            print.end_ctor();
        } else {
            cprint.printValCat(base, print);
            print.output() << fmt::nbsp;
            cprint.printExpr(base, print);
        }

        print.output() << fmt::nbsp;
        cprint.printField(expr->getMemberDecl(), print);
        done(expr, print, cprint);
    }

    void VisitArraySubscriptExpr(const ArraySubscriptExpr* expr,
                                 CoqPrinter& print, ClangPrinter& cprint,
                                 const ASTContext&) {
        print.ctor("Esubscript");
        cprint.printExpr(expr->getLHS(), print);
        print.output() << fmt::nbsp;
        cprint.printExpr(expr->getRHS(), print);
        done(expr, print, cprint);
    }

    void VisitCXXConstructExpr(const CXXConstructExpr* expr, CoqPrinter& print,
                               ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Econstructor");
        // print.output() << expr->isElidable() << fmt::nbsp;
        cprint.printGlobalName(expr->getConstructor(), print);
        print.output() << fmt::nbsp << fmt::lparen;
        for (auto i : expr->arguments()) {
            cprint.printExprAndValCat(i, print);
            print.cons();
        }
        print.end_list();
        //print.output() << fmt::nbsp << expr->isElidable();
        done(expr, print, cprint);
    }

    void VisitCXXMemberCallExpr(const CXXMemberCallExpr* expr,
                                CoqPrinter& print, ClangPrinter& cprint,
                                const ASTContext&) {
        print.ctor("Emember_call");
        auto callee = expr->getCallee()->IgnoreParens();
        auto method = expr->getMethodDecl();
        if (auto me = dyn_cast<MemberExpr>(callee)) {
            print.ctor("inl") << fmt::lparen;
            cprint.printGlobalName(method, print);
            print.output() << "," << fmt::nbsp;
            if (me->hasQualifier() or not method->isVirtual()) {
                // not virtual call
                print.output() << "Direct";
            } else {
                print.output() << "Virtual";
            }
            print.output() << "," << fmt::nbsp;
            cprint.printQualType(me->getMemberDecl()->getType(), print);
            print.output() << fmt::rparen;
            print.end_ctor();

            print.output() << fmt::nbsp;
            assert(me != nullptr &&
                   "member call with MethodDecl must be a MemberExpr");
            if (me->isArrow()) {
                // NOTE: the C++ standard states that a `*` is always an `lvalue`.
                print.output() << fmt::nbsp << "Lvalue";
                print.ctor("Ederef");
                cprint.printExpr(expr->getImplicitObjectArgument(), print);
                print.output() << fmt::nbsp;
                cprint.printQualType(expr->getImplicitObjectArgument()
                                         ->getType()
                                         ->getPointeeType(),
                                     print);
                print.end_ctor();
            } else {
                cprint.printValCat(expr->getImplicitObjectArgument(), print);
                print.output() << fmt::nbsp;
                cprint.printExpr(expr->getImplicitObjectArgument(), print);
            }
        } else if (auto bo = dyn_cast<BinaryOperator>(callee)) {
            assert(bo != nullptr && "expecting a binary operator");
            logging::unsupported() << "member pointers are currently not "
                                      "supported in the logic.\n";
            print.ctor("inr");
            cprint.printExpr(bo->getRHS(), print);
            print.end_ctor() << fmt::nbsp;

            switch (bo->getOpcode()) {
            case BinaryOperatorKind::BO_PtrMemI:
                print.output() << "Lvalue";
                print.ctor("Ederef");
                cprint.printExpr(expr->getImplicitObjectArgument(), print);
                print.output() << fmt::nbsp;
                cprint.printQualType(expr->getImplicitObjectArgument()
                                         ->getType()
                                         ->getPointeeType(),
                                     print);
                print.end_ctor();
                break;
            case BinaryOperatorKind::BO_PtrMemD:
                cprint.printValCat(expr->getImplicitObjectArgument(), print);
                print.output() << fmt::nbsp;
                cprint.printExpr(expr->getImplicitObjectArgument(), print);
                break;
            default:
                assert(false &&
                       "pointer to member function should be a pointer");
            }
        } else {
            assert(false && "no method and not a binary operator");
        }

        print.output() << fmt::nbsp << fmt::lparen;
        for (auto i : expr->arguments()) {
            cprint.printExprAndValCat(i, print);
            print.cons();
        }
        print.end_list();
        done(expr, print, cprint);
    }

    void VisitCXXDefaultArgExpr(const CXXDefaultArgExpr* expr,
                                CoqPrinter& print, ClangPrinter& cprint,
                                const ASTContext&) {
        print.ctor("Eimplicit");
        cprint.printExpr(expr->getExpr(), print);
        done(expr, print, cprint);
    }

    void VisitConditionalOperator(const ConditionalOperator* expr,
                                  CoqPrinter& print, ClangPrinter& cprint,
                                  const ASTContext&) {
        print.ctor("Eif");
        cprint.printExpr(expr->getCond(), print);
        print.output() << fmt::nbsp;
        cprint.printExpr(expr->getTrueExpr(), print);
        print.output() << fmt::nbsp;
        cprint.printExpr(expr->getFalseExpr(), print);
        done(expr, print, cprint);
    }

#if CLANG_VERSION_MAJOR >= 8
    void VisitConstantExpr(const ConstantExpr* expr, CoqPrinter& print,
                           ClangPrinter& cprint, const ASTContext& ctxt) {
        this->Visit(expr->getSubExpr(), print, cprint, ctxt);
    }
#endif

    void VisitParenExpr(const ParenExpr* e, CoqPrinter& print,
                        ClangPrinter& cprint, const ASTContext& ctxt) {
        this->Visit(e->getSubExpr(), print, cprint, ctxt);
    }

    void VisitInitListExpr(const InitListExpr* expr, CoqPrinter& print,
                           ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Einitlist");

        print.begin_list();
        for (auto i : expr->inits()) {
            cprint.printExpr(i, print);
            print.cons();
        }
        print.end_list() << fmt::nbsp;

        if (expr->getArrayFiller()) {
            print.some();
            cprint.printExpr(expr->getArrayFiller(), print);
            print.end_ctor();
        } else {
            print.none();
        }

        done(expr, print, cprint);
    }

    void VisitCXXThisExpr(const CXXThisExpr* expr, CoqPrinter& print,
                          ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Ethis", false);
        done(expr, print, cprint);
    }

    void VisitCXXNullPtrLiteralExpr(const CXXNullPtrLiteralExpr* expr,
                                    CoqPrinter& print, ClangPrinter& cprint,
                                    const ASTContext&) {
        print.output()
            << "Enull"; // note(gmm): null has a special "nullptr_t" type
    }

    void VisitUnaryExprOrTypeTraitExpr(const UnaryExprOrTypeTraitExpr* expr,
                                       CoqPrinter& print, ClangPrinter& cprint,
                                       const ASTContext& ctxt) {
        auto do_arg = [&print, &cprint, &ctxt, expr]() {
            if (expr->isArgumentType()) {
                print.ctor("inl", false);
                cprint.printQualType(expr->getArgumentType(), print);
                print.output() << fmt::rparen;
            } else if (expr->getArgumentExpr()) {
                print.ctor("inr", false);
                cprint.printExpr(expr->getArgumentExpr(), print);
                print.output() << fmt::rparen;
            } else {
                assert(false);
                //fatal("argument to sizeof/alignof is not a type or an expression.");
            }
        };

        if (expr->getKind() == UnaryExprOrTypeTrait::UETT_AlignOf) {
            print.ctor("Ealign_of", false);
            do_arg();
            done(expr, print, cprint);
        } else if (expr->getKind() == UnaryExprOrTypeTrait::UETT_SizeOf) {
            print.ctor("Esize_of", false);
            do_arg();
            done(expr, print, cprint);
        } else {
            using namespace logging;
            fatal() << "unsupported expression `UnaryExprOrTypeTraitExpr` at "
                    << expr->getSourceRange().printToString(
                           ctxt.getSourceManager())
                    << "\n";
            die();
        }
    }

    void
    VisitSubstNonTypeTemplateParmExpr(const SubstNonTypeTemplateParmExpr* expr,
                                      CoqPrinter& print, ClangPrinter& cprint,
                                      const ASTContext& ctxt) {
        this->Visit(expr->getReplacement(), print, cprint, ctxt);
    }

    void VisitCXXNewExpr(const CXXNewExpr* expr, CoqPrinter& print,
                         ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Enew");
        if (expr->getOperatorNew()) {
            print.some();
            cprint.printGlobalName(expr->getOperatorNew(), print);
            print.end_ctor();
        } else {
            print.none();
        }

        print.begin_list();
        for (auto arg : expr->placement_arguments()) {
            cprint.printExprAndValCat(arg, print);
            print.cons();
        }
        print.end_list();

        print.output() << fmt::nbsp;

        cprint.printQualType(expr->getAllocatedType(), print);

        print.output() << fmt::nbsp;

        printOptionalExpr(expr->getArraySize(), print, cprint);

        print.output() << fmt::nbsp;

        if (auto v = expr->getInitializer()) {
            print.some();
            cprint.printExpr(v, print);
            print.end_ctor();
        } else {
            print.none();
        }

        done(expr, print, cprint);
    }

    // todo(gmm): duplicated
    static CXXDestructorDecl* get_dtor(QualType qt) {
        if (auto rd = qt->getAsCXXRecordDecl()) {
            return rd->getDestructor();
        } else if (auto ary = qt->getAsArrayTypeUnsafe()) {
            return get_dtor(ary->getElementType());
        } else {
            return nullptr;
        }
    };

    void VisitCXXDeleteExpr(const CXXDeleteExpr* expr, CoqPrinter& print,
                            ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Edelete");
        print.output() << (expr->isArrayForm() ? "true" : "false") << fmt::nbsp;

        if (expr->getOperatorDelete()) {
            print.some();
            cprint.printGlobalName(expr->getOperatorDelete(), print);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;

        cprint.printExpr(expr->getArgument(), print);

        print.output() << fmt::nbsp;

        cprint.printQualType(expr->getDestroyedType(), print);

        print.output() << fmt::nbsp;

        if (auto dt = get_dtor(expr->getDestroyedType())) {
            print.some();
            cprint.printGlobalName(dt, print);
            print.end_ctor();
        } else {
            print.none();
        }

        done(expr, print, cprint);
    }

    void VisitExprWithCleanups(const ExprWithCleanups* expr, CoqPrinter& print,
                               ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Eandclean");
#ifdef DEBUG
        llvm::errs() << "and_clean objects: " << expr->getNumObjects() << "\n";
        for (const BlockDecl* i : expr->getObjects()) {
            llvm::errs() << static_cast<const void*>(i) << "\n";
        }
#endif /* DEBUG */
        cprint.printExpr(expr->getSubExpr(), print);
        done(expr, print, cprint);
    }

    void VisitMaterializeTemporaryExpr(const MaterializeTemporaryExpr* expr,
                                       CoqPrinter& print, ClangPrinter& cprint,
                                       const ASTContext& ctxt) {
#if 0
	  if (expr->getExtendingDecl()) {
		cprint.printName(expr->getExtendingDecl());
	  } else {
		error() << "no extending decl\n";
	  }
	  error() << "mangling number = " << expr->getManglingNumber() << "\n";
#endif
#if 0
        logging::debug() << "got a 'MaterializeTemporaryExpr' at "
                         << expr->getSourceRange().printToString(
                                ctxt.getSourceManager())
                         << "\n";
        logging::die();
#endif
        if (expr->getExtendingDecl() != nullptr) {
            using namespace logging;
            fatal()
                << "binding a reference to a temporary is not (yet?) supported "
                   "(scope extrusion)"
                << expr->getSourceRange().printToString(ctxt.getSourceManager())
                << "\n";
            die();
        }

        print.ctor("Ematerialize_temp");
#if CLANG_VERSION_MAJOR >= 10
        cprint.printExpr(expr->getSubExpr(), print);
#else
        cprint.printExpr(expr->GetTemporaryExpr(), print);
#endif
        done(expr, print, cprint);
    }

    void VisitCXXBindTemporaryExpr(const CXXBindTemporaryExpr* expr,
                                   CoqPrinter& print, ClangPrinter& cprint,
                                   const ASTContext&) {
        print.ctor("Ebind_temp");
        cprint.printExpr(expr->getSubExpr(), print);
        print.output() << fmt::nbsp;
        cprint.printGlobalName(expr->getTemporary()->getDestructor(), print);
        done(expr, print, cprint);
    }

    void VisitCXXTemporaryObjectExpr(const CXXTemporaryObjectExpr* expr,
                                     CoqPrinter& print, ClangPrinter& cprint,
                                     const ASTContext&) {
        // todo(gmm): initialization semantics?
        print.ctor("Econstructor");
        // print.output() << expr->isElidable() << fmt::nbsp;
        cprint.printGlobalName(expr->getConstructor(), print);
        print.output() << fmt::nbsp;

        print.begin_list();
        for (auto i : expr->arguments()) {
            cprint.printExprAndValCat(i, print);
            print.cons();
        }
        print.end_list();

        //print.output() << fmt::nbsp << expr->isElidable();

        done(expr, print, cprint);
    }

    void VisitOpaqueValueExpr(const OpaqueValueExpr* expr, CoqPrinter& print,
                              ClangPrinter& cprint, const ASTContext&) {
        cprint.printExpr(expr->getSourceExpr(), print);
    }

    void VisitAtomicExpr(const clang::AtomicExpr* expr, CoqPrinter& print,
                         ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Eatomic");

        switch (expr->getOp()) {
#define BUILTIN(ID, TYPE, ATTRS)
#define ATOMIC_BUILTIN(ID, TYPE, ATTRS)                                        \
    case clang::AtomicExpr::AO##ID:                                            \
        print.output() << "AO" #ID << fmt::nbsp;                               \
        break;
#include "clang/Basic/Builtins.def"
#undef BUILTIN
#undef ATOMIC_BUILTIN
        }

        print.begin_list();
        for (unsigned i = 0; i < expr->getNumSubExprs(); ++i) {
            cprint.printExprAndValCat(expr->getSubExprs()[i], print);
            print.cons();
        }
        print.end_list();

        done(expr, print, cprint);
    }

    void VisitCXXDefaultInitExpr(const CXXDefaultInitExpr* expr,
                                 CoqPrinter& print, ClangPrinter& cprint,
                                 const ASTContext&) {
        print.ctor("Edefault_init_expr");
        cprint.printExpr(expr->getExpr(), print);
        print.end_ctor();
    }

    void VisitPredefinedExpr(const PredefinedExpr* expr, CoqPrinter& print,
                             ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Estring");
        print.str(expr->getFunctionName()->getString());
        done(expr, print, cprint);
    }

    void VisitVAArgExpr(const VAArgExpr* expr, CoqPrinter& print,
                        ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Eva_arg");
        cprint.printExpr(expr->getSubExpr(), print);
        done(expr, print, cprint);
    }

    void VisitLambdaExpr(const LambdaExpr* expr, CoqPrinter& print,
                         ClangPrinter& cprint, const ASTContext&) {
        print.ctor("Eunsupported");
        print.str("lambda");
        done(expr, print, cprint);
    }

    void VisitImplicitValueInitExpr(const ImplicitValueInitExpr* expr,
                                    CoqPrinter& print, ClangPrinter& cprint,
                                    const ASTContext& ctxt) {
        print.ctor("Eimplicit_init");
        done(expr, print, cprint);
    }

    void VisitCXXPseudoDestructorExpr(const CXXPseudoDestructorExpr* expr,
                                      CoqPrinter& print, ClangPrinter& cprint,
                                      const ASTContext& ctxt) {
        print.ctor("Epseudo_destructor");
        cprint.printQualType(expr->getDestroyedType(), print);
        print.output() << fmt::nbsp;
        cprint.printExpr(expr->getBase(), print);
        print.end_ctor();
    }

    void VisitCXXNoexceptExpr(const CXXNoexceptExpr* expr, CoqPrinter& print,
                              ClangPrinter& cprint, const ASTContext&) {
        // note: i should record the fact that this is a noexcept expression
        print.ctor("Ebool");
        print.boolean(expr->getValue());
        print.end_ctor();
    }

    void VisitTypeTraitExpr(const TypeTraitExpr* expr, CoqPrinter& print,
                            ClangPrinter& cprint, const ASTContext&) {
        // note: i should record the fact that this is a noexcept expression
        print.ctor("Ebool");
        print.boolean(expr->getValue());
        print.end_ctor();
    }

    void VisitCXXScalarValueInitExpr(const CXXScalarValueInitExpr* expr,
                                     CoqPrinter& print, ClangPrinter& cprint,
                                     const ASTContext&) {
        print.ctor("Eimplicit_init");
        cprint.printQualType(expr->getType(), print);
        print.end_ctor();
    }
};

PrintExpr PrintExpr::printer;

void
ClangPrinter::printExpr(const clang::Expr* expr, CoqPrinter& print) {
    auto depth = print.output().get_depth();
    PrintExpr::printer.Visit(expr, print, *this, *this->context_);
    if (depth != print.output().get_depth()) {
        using namespace logging;
        fatal() << "indentation bug in during: " << expr->getStmtClassName()
                << "\n";
        assert(false);
    }
}
