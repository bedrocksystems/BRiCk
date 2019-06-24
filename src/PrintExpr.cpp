/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include "CoqPrinter.hpp"
#include "ClangPrinter.hpp"
#include "clang/AST/Mangle.h"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/Version.inc"
#include "clang/AST/StmtVisitor.h"
#include <Formatter.hpp>

using namespace clang;
using namespace fmt;

void printCastKind(Formatter& out, const CastKind ck) {
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
	} else if (ck == CastKind::CK_DerivedToBase
			|| ck == CastKind::CK_UncheckedDerivedToBase) {
		out << "Cderived2base";
	} else if (ck == CastKind::CK_BaseToDerived) {
		out << "Cbase2derived";
	} else if (ck == CastKind::CK_ToVoid) {
		out << "C2void";
  } else {
#if CLANG_VERSION_MAJOR >= 7
		llvm::errs() << "unsupported cast kind \""
				<< CastExpr::getCastKindName(ck) << "\"\n";
#else
		llvm::errs() << "unsupported cast kind ..." << ck << "\n";
#endif
		out << "Cunsupported";
	}
}

class PrintExpr : public ConstStmtVisitor<PrintExpr, void, CoqPrinter &, ClangPrinter &> {
  private:

  void done(const Expr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.output() << fmt::nbsp;
    cprint.printQualType(expr->getType(), print);
    print.end_ctor();
  }
public:
  static PrintExpr printer;

  void VisitStmt(const Stmt *stmt, CoqPrinter &print, ClangPrinter &)
  {
    print.error() << "while printing an expr, got a statement '"
                  << stmt->getStmtClassName() << "'\n";
  }

  void VisitExpr(const Expr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.error() << "unrecognized expression '" << expr->getStmtClassName() << "'\n";
  }

  void printBinaryOperator(BinaryOperator::Opcode op, StringRef def, CoqPrinter& print)
  {
    switch (op) {
#define CASE(k, s)                                                             \
  case BinaryOperatorKind::BO_##k:                                             \
    print.output() << s;                                                       \
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
#undef CASE
    default:
      print.error() << "defaulting binary operator\n";
      print.ctor("Bother") << "\"" << def << "\"" << fmt::rparen;
      break;
    }
  }

  void VisitBinaryOperator(const BinaryOperator *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
#define ACASE(k, v)                                                            \
  case BinaryOperatorKind::BO_##k##Assign:                                     \
    print.ctor("Eassign_op") << #v << fmt::nbsp;                                     \
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
      printBinaryOperator(expr->getOpcode(), expr->getOpcodeStr(), print);
      print.output() << fmt::nbsp;
      break;
    }
#undef ACASE
    cprint.printExpr(expr->getLHS(), print);
    print.output() << fmt::nbsp;
    cprint.printExpr(expr->getRHS(), print);
    done(expr, print, cprint);
  }

  void VisitDependentScopeDeclRefExpr(const DependentScopeDeclRefExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    ConstStmtVisitor<PrintExpr, void, CoqPrinter&, ClangPrinter&>::VisitDependentScopeDeclRefExpr(expr, print, cprint);
  }

  void printUnaryOperator(UnaryOperator::Opcode op, CoqPrinter& print)
  {
    switch (op) {
#define CASE(k, s)                                                             \
  case UnaryOperatorKind::UO_##k:                                              \
    print.output() << s;                                                             \
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
      print.error() << "unsupported unary operator\n";
      print.output() << "(Uother \"" << UnaryOperator::getOpcodeStr(op) << "\")";
      break;
    }
  }

  void VisitUnaryOperator(const UnaryOperator *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
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

  void VisitDeclRefExpr(const DeclRefExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    if (isa<EnumConstantDecl>(expr->getDecl())) {
      print.ctor("Econst_ref", false);
    } else {
      print.ctor("Evar", false);
    }
    cprint.printName(expr->getDecl(), print);
    done(expr, print, cprint);
  }

  void VisitCallExpr(const CallExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
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

  void VisitCastExpr(const CastExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    if (auto cf = expr->getConversionFunction()) {
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

  void VisitImplicitCastExpr(const ImplicitCastExpr *expr, CoqPrinter& print, ClangPrinter& cprint) {
    // todo(gmm): this is a complete hack!
    if (auto ref = dyn_cast<DeclRefExpr>(expr->getSubExpr())) {
      if (ref->getDecl()->isImplicit()) {
        // assume that this is a builtin
        print.ctor("Evar");
        print.ctor("Gname", false);
        cprint.printGlobalName(ref->getDecl(), print);
        print.end_ctor();
        done(expr, print, cprint);
        return;
      }
    }
    VisitCastExpr(expr, print, cprint);
  }

  void VisitCXXNamedCastExpr(const CXXNamedCastExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    if (expr->getConversionFunction()) {
      return VisitCastExpr(expr, print, cprint);
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
      auto from = expr->getSubExpr()->getType().getTypePtr()->getPointeeCXXRecordDecl();
      auto to = expr->getType().getTypePtr()->getPointeeCXXRecordDecl();
      if (from && to) {
        print.ctor("Cstatic", false);
        cprint.printGlobalName(from, print);
        print.output() << fmt::nbsp;
        cprint.printGlobalName(to, print);
        print.end_ctor();
      } else {
        print.output() << "Cbad";
      }
    } else if (isa<CXXDynamicCastExpr>(expr)) {
      auto from = expr->getSubExpr()->getType().getTypePtr()->getPointeeCXXRecordDecl();
      auto to = expr->getType().getTypePtr()->getPointeeCXXRecordDecl();
      if (from && to) {
        print.ctor("Cdynamic", false);
        cprint.printGlobalName(from, print);
        print.output() << fmt::nbsp;
        cprint.printGlobalName(to, print);
        print.end_ctor();
      } else {
        print.output() << "Cbad";
      }
    } else {
      print.error() << "unknown named cast\n";
      llvm::errs().flush();
      assert(false);
    }
    print.output() << fmt::nbsp;

    cprint.printExprAndValCat(expr->getSubExpr(), print);
    done(expr, print, cprint);
  }

  void VisitIntegerLiteral(const IntegerLiteral *lit, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Eint", false) << lit->getValue() << fmt::nbsp;
    done(lit, print, cprint);
  }

  void VisitCharacterLiteral(const CharacterLiteral *lit, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Echar", false);
    print.ascii(lit->getValue());
    print.output() << fmt::nbsp;
    done(lit, print, cprint);
  }

  void VisitStringLiteral(const StringLiteral *lit, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Estring", false) << "\"" << lit->getBytes() << "\"";
    done(lit, print, cprint);
  }

  void VisitCXXBoolLiteralExpr(const CXXBoolLiteralExpr *lit, CoqPrinter& print, ClangPrinter& cprint)
  {
    if (lit->getValue()) {
      print.output() << "(Ebool true)";
    } else {
      print.output() << "(Ebool false)";
    }
  }

  void printField(const ValueDecl *decl, CoqPrinter& print, ClangPrinter& cprint) {
    if (const FieldDecl *f = dyn_cast<clang::FieldDecl>(decl)) {
      print.output() << "{| f_type :=" << fmt::nbsp;
      cprint.printGlobalName(f->getParent(), print);
      print.output() << fmt::nbsp << "; f_name := ";

      if (decl->getName() == "") {
        const CXXRecordDecl *rd = f->getType()->getAsCXXRecordDecl();
        assert(rd && "unnamed field must be a record");
        print.ctor("Nanon", false);
        cprint.printGlobalName(rd, print);
        print.end_ctor();
      } else {
        print.str(decl->getName());
      }
      print.output() << " |}";
    } else if (const CXXMethodDecl *meth = dyn_cast<clang::CXXMethodDecl>(decl)) {
      print.output() << "{| f_type :=" << fmt::nbsp;
      cprint.printGlobalName(meth->getParent(), print);
      print.output() << fmt::nbsp << "; f_name := \"" << decl->getNameAsString() << "\" |}";
    } else {
      print.error() << "member not pointing to field "
                    << decl->getDeclKindName() << "\n";
      assert(false && "member not pointing to field");
    }
  }

  void VisitMemberExpr(const MemberExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Emember");

    auto base = expr->getBase();
    if (expr->isArrow()) {
      print.ctor("Ederef");
      cprint.printExpr(base, print);
      done(base, print, cprint);
    } else {
      cprint.printExpr(base, print);
    }

    print.output() << fmt::nbsp;
    printField(expr->getMemberDecl(), print, cprint);
    done(expr, print, cprint);
  }

  void VisitArraySubscriptExpr(const ArraySubscriptExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Esubscript");
    cprint.printExpr(expr->getLHS(), print);
    print.output() << fmt::nbsp;
    cprint.printExpr(expr->getRHS(), print);
    done(expr, print, cprint);
  }

  void VisitCXXConstructExpr(const CXXConstructExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Econstructor");
    // print.output() << expr->isElidable() << fmt::nbsp;
    cprint.printGlobalName(expr->getConstructor(), print);
    print.output() << fmt::nbsp << fmt::lparen;
    for (auto i : expr->arguments()) {
      cprint.printExprAndValCat(i, print);
      print.cons();
    }
    print.end_list();
    done(expr, print, cprint);
  }

  void VisitCXXMemberCallExpr(const CXXMemberCallExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    auto method = expr->getMethodDecl();
    print.ctor("Emember_call");
    print.output() << (method->isVirtual() ? "true" : "false") << fmt::nbsp;
    cprint.printGlobalName(method, print);
    print.output() << fmt::nbsp;
    auto me = dyn_cast<MemberExpr>(expr->getCallee());
    if (me->isArrow()) {
      print.ctor("Ederef");
      cprint.printExpr(expr->getImplicitObjectArgument(), print);
      done(expr->getImplicitObjectArgument(), print, cprint);
    } else {
      cprint.printExpr(expr->getImplicitObjectArgument(), print);
    }

    print.output() << fmt::nbsp << fmt::lparen;
    for (auto i : expr->arguments()) {
      cprint.printExprAndValCat(i, print);
      print.cons();
    }
    print.end_list();
    done(expr, print, cprint);
  }

  void VisitCXXDefaultArgExpr(const CXXDefaultArgExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Eimplicit");
    cprint.printExpr(expr->getExpr(), print);
    done(expr, print, cprint);
  }

  void VisitConditionalOperator(const ConditionalOperator *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Eif");
    cprint.printExpr(expr->getCond(), print);
    print.output() << fmt::nbsp;
    cprint.printExpr(expr->getTrueExpr(), print);
    print.output() << fmt::nbsp;
    cprint.printExpr(expr->getFalseExpr(), print);
    done(expr, print, cprint);
  }

#if CLANG_VERSION_MAJOR >= 8
  void VisitConstantExpr(const ConstantExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    this->Visit(expr->getSubExpr(), print, cprint);
  }
#endif

  void VisitParenExpr(const ParenExpr *e, CoqPrinter& print, ClangPrinter& cprint)
  {
    this->Visit(e->getSubExpr(), print, cprint);
  }

  void VisitInitListExpr(const InitListExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Einitlist");
    print.begin_list();
    for (auto i : expr->inits()) {
      cprint.printExpr(i, print);
      print.cons();
    }
    print.end_list();
    done(expr, print, cprint);
  }

  void VisitCXXThisExpr(const CXXThisExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Ethis", false);
    done(expr, print, cprint);
  }

  void VisitCXXNullPtrLiteralExpr(const CXXNullPtrLiteralExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.output() << "Enull"; // note(gmm): null has a special "nullptr_t" type
  }

  void VisitUnaryExprOrTypeTraitExpr(const UnaryExprOrTypeTraitExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    auto do_arg = [&print, &cprint, expr]() {
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

    // todo(gmm): is there any benefit to not just desugaring `sizeof(e)` into
    // `sizeof(t)` where `t` is the type of `e`?
    // similarly for `alignof`?
    if (expr->getKind() == UnaryExprOrTypeTrait::UETT_AlignOf) {
      print.ctor("Ealign_of", false);
      do_arg();
      done(expr, print, cprint);
    } else if (expr->getKind() == UnaryExprOrTypeTrait::UETT_SizeOf) {
      print.ctor("Esize_of", false);
      do_arg();
      done(expr, print, cprint);
    } else {
      print.error() << "unsupported expression `UnaryExprOrTypeTraitExpr`\n";
    }
  }

  void VisitSubstNonTypeTemplateParmExpr(
          const SubstNonTypeTemplateParmExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    this->Visit(expr->getReplacement(), print, cprint);
  }

  void VisitCXXNewExpr(const CXXNewExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Enew");
    if (expr->getOperatorNew()) {
      print.ctor("Some", false);
      cprint.printGlobalName(expr->getOperatorNew(), print);
      print.output() << fmt::rparen;
    } else {
      print.output() << "None";
    }

    print.output() << fmt::nbsp;

    if (auto v = expr->getArraySize()) {
      print.ctor("Some");
      cprint.printExpr(v, print);
      print.output() << fmt::rparen;
    } else {
      print.none();
    }

    print.output() << fmt::nbsp;

    if (auto v = expr->getConstructExpr()) {
      print.ctor("Some");
      cprint.printExpr(v, print);
      print.output() << fmt::rparen;
    } else {
      print.none();
    }

    done(expr, print, cprint);
  }

  void VisitCXXDeleteExpr(const CXXDeleteExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Edelete");
    print.output() << (expr->isArrayForm() ? "true" : "false") << fmt::nbsp;

    if (expr->getOperatorDelete()) {
      print.ctor("Some", false);
      cprint.printGlobalName(expr->getOperatorDelete(), print);
      print.output() << fmt::rparen;
    } else {
      print.output() << "None";
    }
    print.output() << fmt::nbsp;

    cprint.printExpr(expr->getArgument(), print);

    done(expr, print, cprint);
  }

  void VisitExprWithCleanups(const ExprWithCleanups *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Eandclean");
    cprint.printExpr(expr->getSubExpr(), print);
    done(expr, print, cprint);
  }

  void VisitMaterializeTemporaryExpr(const MaterializeTemporaryExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
#if 0
	  if (expr->getExtendingDecl()) {
		cprint.printName(expr->getExtendingDecl());
	  } else {
		error() << "no extending decl\n";
	  }
	  error() << "mangling number = " << expr->getManglingNumber() << "\n";
#endif
    print.ctor("Ematerialize_temp");
    cprint.printExpr(expr->GetTemporaryExpr(), print);
    done(expr, print, cprint);
  }

  void VisitCXXTemporaryObjectExpr(const CXXTemporaryObjectExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    print.ctor("Econstructor");
    // print.output() << expr->isElidable() << fmt::nbsp;
    cprint.printGlobalName(expr->getConstructor(), print);
    print.output() << fmt::nbsp;

    print.begin_list();
    for (auto i : expr->arguments()) {
      cprint.printExpr(i, print);
      print.cons();
    }
    print.end_list();

    done(expr, print, cprint);
  }

  void VisitOpaqueValueExpr(const OpaqueValueExpr *expr, CoqPrinter& print, ClangPrinter& cprint)
  {
    cprint.printExpr(expr->getSourceExpr(), print);
  }

  void VisitAtomicExpr(const clang::AtomicExpr *expr, CoqPrinter& print, ClangPrinter& cprint) {
    print.ctor("Eatomic");

    switch (expr->getOp()) {
    #define BUILTIN(ID, TYPE, ATTRS)
    #define ATOMIC_BUILTIN(ID, TYPE, ATTRS) case clang::AtomicExpr::AO ## ID: print.output() << "AO" #ID << fmt::nbsp; break;
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
};

PrintExpr PrintExpr::printer;

void
ClangPrinter::printExpr(const clang::Expr* expr, CoqPrinter& print) {
  auto depth = print.output().get_depth();
  PrintExpr::printer.Visit(expr, print, *this);
  if (depth != print.output().get_depth()) {
    llvm::errs() << "indentation bug in during: " << expr->getStmtClassName() << "\n";
    assert(false);
  }
}
