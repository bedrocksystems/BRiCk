#include <list>
#include <Formatter.hpp>
#include "clang/Basic/Version.inc"
#include "clang/AST/Type.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Mangle.h"
#include "TypeVisitorWithArgs.h"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "CommentScanner.hpp"

using namespace clang;
using namespace fmt;

void
printCastKind (Formatter& out, const CastKind ck) {
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
  } else if (ck == CastKind::CK_DerivedToBase || ck == CastKind::CK_UncheckedDerivedToBase) {
    out << "Cderived2base";
  } else if (ck == CastKind::CK_BaseToDerived) {
    out << "Cbase2derived";
  } else if (ck == CastKind::CK_ToVoid) {
	out << "C2void";
  } else {
#if CLANG_VERSION_MAJOR >= 7
	llvm::errs() << "unsupported cast kind \"" << CastExpr::getCastKindName(ck)
		<< "\"\n";
#else
	llvm::errs() << "unsupported cast kind ..." << ck << "\n";
#endif
	out << "Cunsupported";
  }
}

#define DELEGATE_OUTPUT(parent) \
  fmt::Formatter& output() const { return parent->output(); } \
  llvm::raw_ostream& error () const { return llvm::errs(); } \
  fmt::Formatter& ctor(const char* ctor, bool line=true) { return parent->ctor(ctor, line); }

#define DELEGATE_OUTPUT_I(parent) \
  fmt::Formatter& output() { return parent; } \
  llvm::raw_ostream& error () const { return llvm::errs(); }

#define PRINT_LIST(iterator, fn) \
	output() << "[" << fmt::indent; \
    for (auto i = iterator##_begin(), e = iterator##_end(); i != e; ) { \
	  fn(*i); \
	  if (++i != e) { \
	      output() << ";" << fmt::line; \
	  } \
    } \
	output() << fmt::outdent << "]";

#define OPTIONAL(p, v) \
	if (v) { \
      ctor("Some"); p(v); output() << fmt::rparen; \
	} else { \
	  output() << "None"; \
	}

/*
 * note(gmm): ideally, i wouldn't really need nested classes here, instead
 * i would just pass the `Formatter` argument to each of the classes and everything
 * would be top-level definitions. however, Clang doesn't permit arguments to all
 * of their visitors (only to `StmtVisitor`) so instead we have to have a configuration
 * and then maintain pointers to it everywhere.
 */
class ToCoq
{
private:
  Formatter &out;
  DiagnosticsEngine engine;
  MangleContext * mangleContext;

  DELEGATE_OUTPUT_I(out)

  // todo(gmm): this should move to Formatter
  fmt::Formatter&
  ctor(const char* ctor, bool line=true) {
	if (line) {
	  output() << fmt::line;
	}
	return output() << fmt::lparen << ctor << fmt::nbsp;
  }

  class PrintType : public TypeVisitor<PrintType, void>
  {
  private:
	ToCoq *const parent;

	DELEGATE_OUTPUT(parent)

  public:
	PrintType (ToCoq *_parent)
		: parent(_parent) {
	}

	void
	VisitType (const Type* type) {
	  error() << "[ERR] unsupported type: ";
	  type->dump(error());
	  error() << "\n";
	  output() << "(Tunknown \"" << type->getTypeClassName() << "\")";
	}

	void
	VisitTemplateTypeParmType(const TemplateTypeParmType *type) {
	  ctor("Ttemplate") << "\"" << type->getDecl()->getNameAsString() << "\"" << fmt::rparen;
	}

	void
	VisitEnumType (const EnumType* type) {
	  ctor("Tref");
	  parent->printGlobalName(type->getDecl());
	  output() << fmt::rparen;
	}
	void
	VisitRecordType (const RecordType *type) {
	  ctor("Tref");
	  parent->printGlobalName(type->getDecl());
	  output() << fmt::rparen;
	}

	void
	VisitParenType (const ParenType* type) {
	  parent->printQualType(type->getInnerType());
	}

	void
	VisitBuiltinType (const BuiltinType* type) {
	  // todo(gmm): record bitwidths from the context when they are defaulted.
	  if (type->getKind() == BuiltinType::Kind::Bool) {
		output() << "Tbool";
	  } else if (type->getKind() == BuiltinType::Kind::Int128) {
		output() << "T_int128";
	  } else if (type->getKind() == BuiltinType::Kind::UInt128) {
		output() << "T_uint128";
	  } else if (type->getKind() == BuiltinType::Kind::Int) {
		output() << "T_int";
	  } else if (type->getKind() == BuiltinType::Kind::UInt) {
		output() << "T_uint";
	  } else if (type->getKind() == BuiltinType::Kind::ULong) {
		output() << "T_ulong";
	  } else if (type->getKind() == BuiltinType::Kind::UShort) {
		output() << "T_ushort";
	  } else if (type->getKind() == BuiltinType::Kind::Long) {
		output() << "T_long";
	  } else if (type->getKind() == BuiltinType::Kind::LongDouble) {
	  	output() << "T_long_double";
	  } else if (type->getKind() == BuiltinType::Kind::LongLong) {
		output() << "T_longlong";
	  } else if (type->getKind() == BuiltinType::Kind::ULongLong) {
		output() << "T_ulonglong";
	  } else if (type->getKind() == BuiltinType::Kind::Short) {
		output() << "T_short";
	  } else if (type->getKind() == BuiltinType::Kind::Char16) {
		output() << "T_char16";
	  } else if (type->getKind() == BuiltinType::Kind::Char_S) {
		output() << "(Tchar (Some " << parent->Context->getCharWidth() << ") true)";
	  } else if (type->getKind() == BuiltinType::Kind::SChar) {
		output() << "(Tchar (Some " << parent->Context->getCharWidth() << ") true)";
	  } else if (type->getKind() == BuiltinType::Kind::UChar) {
		output() << "(Tchar (Some " << parent->Context->getCharWidth() << ") false)";
	  } else if (type->getKind() == BuiltinType::Kind::Char_U) {
		output() << "(Tchar (Some " << parent->Context->getCharWidth() << ") false)";
	  } else if (type->getKind() == BuiltinType::Kind::Char8) {
		output() << "T_char8";
	  } else if (type->getKind() == BuiltinType::Kind::Char32) {
		output() << "T_char32";
	  } else if (type->getKind() == BuiltinType::Kind::Void) {
		output() << "Tvoid";
	  } else {
		error() << "Unsupported type \""
			    << type->getNameAsCString(PrintingPolicy(LangOptions())) << "\"\n";
		output() << "Tunknown";
	  }
	}

	void
	VisitReferenceType (const ReferenceType* type) {
	  ctor("Treference");
	  parent->printQualType(type->getPointeeType());
	  output() << fmt::rparen;
	}

	void
	VisitPointerType (const PointerType* type) {
	  ctor("Tpointer");
	  parent->printQualType(type->getPointeeType());
	  output() << fmt::rparen;
	}

	void
	VisitTypedefType (const TypedefType *type) {
	  ctor("Tref");
	  parent->printGlobalName(type->getDecl());
	  output() << fmt::rparen;
	}

	void
	VisitFunctionProtoType (const FunctionProtoType *type) {
	  ctor("Tfunction");
	  parent->printQualType(type->getReturnType());
	  output() << fmt::nbsp << "[" << fmt::indent;
	  for (auto i = type->param_type_begin(), e = type->param_type_end();
		  i != e;) {
		parent->printQualType(*i);
		if (++i != e) {
		  output() << ";" << fmt::nbsp;
		}
	  }
	  output() << "]" << fmt::rparen;
	}

	void
	VisitElaboratedType(const ElaboratedType *type) {
	  parent->printQualType(type->getNamedType());
	}

	void
	VisitConstantArrayType(const ConstantArrayType *type) {
	  ctor("Tarray");
	  parent->printQualType(type->getElementType());
	  output() << fmt::nbsp;
	  output() << "(Some " << type->getSize().getLimitedValue() << ")" << fmt::rparen;
	}

	void
	VisitSubstTemplateTypeParmType(const SubstTemplateTypeParmType *type) {
	  parent->printQualType(type->getReplacementType());
	}

	void
	VisitIncompleteArrayType(const IncompleteArrayType *type) {
	  // note(gmm): i might want to note the sugar.
	  ctor("Qconst");
	  ctor("Tpointer");
	  parent->printQualType(type->getElementType());
	  output() << fmt::rparen << fmt::rparen;
	}

	void
	VisitDecayedType(const DecayedType *type) {
	  parent->printQualType(type->getPointeeType());
	}

	void
	VisitTemplateSpecializationType(const TemplateSpecializationType *type) {
	  ctor("Tref");
	  output() << "\"";
	  parent->mangleContext->mangleCXXName(type->getAsCXXRecordDecl(), parent->out.nobreak());
	  output() << "\"" << fmt::rparen;
	}
  };

  class PrintLocalDecl : public ConstDeclVisitorArgs<PrintLocalDecl, void>
  {
  private:
	ToCoq *const parent;

	DELEGATE_OUTPUT(parent)

  public:
	PrintLocalDecl (ToCoq *_parent)
		: parent(_parent) {
	}
	void
	VisitVarDecl (const VarDecl *decl) {
	  output() << fmt::lparen << "\"" << decl->getNameAsString() << "\"," << fmt::nbsp;
	  parent->printQualType(decl->getType());
	  output() << "," << fmt::nbsp;
	  if (decl->hasInit()) {
		output() << fmt::line << fmt::lparen << "Some" << fmt::nbsp;
		parent->printExpr(decl->getInit());
		output() << fmt::rparen;
	  } else {
		output() << fmt::nbsp << "None";
	  }
	  output() << fmt::rparen;
	}

	void
	VisitDecl (const Decl *decl) {
	  error() << "unexpected local declaration";
	}
  };

  class PrintParam : public ConstDeclVisitorArgs<PrintParam, void>
  {
  private:
	ToCoq *const parent;

	DELEGATE_OUTPUT(parent)

  public:
	PrintParam (ToCoq *_parent)
		: parent(_parent) {
	}
	void
	VisitParmVarDecl (const ParmVarDecl *decl) {
	  output() << fmt::lparen << "\"" << decl->getNameAsString() << "\"," << fmt::nbsp;
	  parent->printQualType(decl->getType());
	  output() << fmt::rparen;
	}

	void
	VisitDecl (const Decl *decl) {
	  error() << "unexpected local declaration";
	}
  };

  class PrintStmt : public ConstStmtVisitor<PrintStmt, void>
  {
  private:
	ToCoq *const parent;

	DELEGATE_OUTPUT(parent)
  public:
	PrintStmt (ToCoq *_parent)
		: parent(_parent) {
	}

	void
	VisitStmt(const Stmt *stmt) {
	  error() << "unsupported statement " << stmt->getStmtClassName() << "\n";
	}

	void
	VisitDeclStmt (const DeclStmt* stmt) {
	  ctor("Sdecl");
	  PRINT_LIST(stmt->decl, parent->printLocalDecl)
	  output() << fmt::rparen;
	}

	void
	VisitWhileStmt (const WhileStmt* stmt) {
	  ctor("Swhile");
	  if (stmt->getConditionVariable()) {
		error() << "unsupported variable declaration in while";
	  }
	  parent->printExpr(stmt->getCond());
	  output() << fmt::nbsp;
	  parent->printStmt(stmt->getBody());
	  output() << fmt::rparen;
	}

	void
	VisitForStmt (const ForStmt* stmt) {
	  ctor("Sfor");
	  OPTIONAL(parent->printStmt, stmt->getInit())
	  output() << fmt::nbsp;
	  OPTIONAL(parent->printExpr, stmt->getCond())
	  output() << fmt::nbsp;
	  OPTIONAL(parent->printExpr, stmt->getInc())
	  output() << fmt::nbsp;
	  parent->printStmt(stmt->getBody());
	  output() << fmt::rparen;
	}

	void
	VisitDoStmt (const DoStmt* stmt) {
	  ctor("Sdo");
	  parent->printStmt(stmt->getBody());
	  output() << fmt::nbsp;
	  parent->printExpr(stmt->getCond());
	  output() << fmt::rparen;
	}

	void
	VisitBreakStmt(const BreakStmt* stmt) {
	  output() << "Sbreak";
	}

	void
	VisitContinueStmt(const ContinueStmt* stmt) {
	  output() << "Scontinue";
	}

	void
	VisitIfStmt (const IfStmt* stmt) {
	  ctor("Sif");
	  if (stmt->getConditionVariable()) {
		ctor("Some");
		parent->printLocalDecl(stmt->getConditionVariable());
		output() << fmt::rparen;
	  } else {
		output() << "None";
	  }
	  output() << fmt::nbsp;
	  parent->printExpr(stmt->getCond());
	  output() << fmt::nbsp;
	  parent->printStmt(stmt->getThen());
	  output() << fmt::nbsp;
	  if (stmt->getElse()) {
		parent->printStmt(stmt->getElse());
	  } else {
		output() << "Sskip";
	  }
	  output() << fmt::rparen;
	}

	void
	VisitSwitchStmt(const SwitchStmt *stmt) {
	  ctor("Sswitch");
	  parent->printExpr(stmt->getCond());
	  const SwitchCase *sc = stmt->getSwitchCaseList();
	  output() << fmt::lparen;
	  while (sc) {
		output() << fmt::lparen;
		if (isa<DefaultStmt>(sc)) {
		  output() << "Default";
		} else if (auto cs = dyn_cast<CaseStmt>(sc)) {
		  if (cs->getRHS()) {
			output() << "Range" << fmt::nbsp;
			parent->printExpr(cs->getLHS());
			output() << fmt::nbsp;
			parent->printExpr(cs->getRHS());
		  } else {
			output() << "Exact" << fmt::nbsp;
			parent->printExpr(cs->getLHS());
		  }
		} else {
		  error() << "switch body not default or case.\n";
		  llvm::errs().flush();
		  assert(false);
		}
		output() << "," << fmt::nbsp;
	    parent->printStmt(sc->getSubStmt());
	    output() << fmt::rparen;

		sc = sc->getNextSwitchCase();
	  }
	  output() << "::nil" << fmt::rparen << fmt::rparen;
	}

	void
	VisitExpr (const Expr *expr) {
	  ctor("Sexpr");
	  parent->printExpr(expr);
	  output() << fmt::rparen;
	}

	void
	VisitReturnStmt (const ReturnStmt *stmt) {
	  if (stmt->getRetValue() != nullptr) {
		ctor("Sreturn (Some");
		parent->printExpr(stmt->getRetValue());
		output() << ")" << fmt::rparen;
	  } else {
		output() << "(Sreturn None)";
	  }
	}

	void
	VisitCompoundStmt (const CompoundStmt *stmt) {
	  ctor("Sseq");
	  PRINT_LIST(stmt->body, parent->printStmt)
	  output() << fmt::rparen;
	}

	void
	VisitNullStmt (const NullStmt *stmt) {
	  output() << "Sskip";
	}

	void
	VisitGCCAsmStmt (const GCCAsmStmt *stmt) {
	  // todo(gmm): more to do here to support assembly
	  ctor("Sasm") << "\"" << stmt->getAsmString()->getString() << "\"";
	  output() << fmt::rparen;
	}
  };

  class PrintExpr : public ConstStmtVisitor<PrintExpr, void>
  {
  private:
	ToCoq *const parent;
	DELEGATE_OUTPUT(parent)
  public:
	PrintExpr (ToCoq *_parent)
		: parent(_parent) {
	}

	void
	VisitStmt (const Stmt* stmt) {
	  error() << "while printing an expr, got a statement '"
		  << stmt->getStmtClassName() << "'\n";
	}

	void
	VisitExpr (const Expr* expr) {
	  error() << "unrecognized expression '"
		      << expr->getStmtClassName() << "'\n";
	}

	void
	printBinaryOperator(BinaryOperator::Opcode op, StringRef def) {
	  switch (op) {
#define CASE(k, s) \
		case BinaryOperatorKind::BO_##k: output() << s; break;
		CASE(Add, "Badd")
		CASE(AddAssign, "(Bop_assign Badd)")
		CASE(And, "Band")
		CASE(AndAssign, "(Bop_assign Band)")
		CASE(Cmp, "Bcmp")
		CASE(Div, "Bdiv")
		CASE(DivAssign, "(Bop_assign Bdiv)")
		CASE(EQ, "Beq")
		CASE(GE, "Bge")
		CASE(GT, "Bgt")
		CASE(LE, "Ble")
		CASE(LT, "Blt")
		CASE(Mul, "Bmul")
		CASE(MulAssign, "(Bop_assign Bmul)")
		CASE(NE, "Bneq")
		CASE(Or, "Bor")
		CASE(OrAssign, "(Bop_assign Bor)")
		CASE(Rem, "Bmod")
		CASE(RemAssign, "(Bop_assign Bmod)")
		CASE(Shl, "Bshl")
		CASE(ShlAssign, "(Bop_assign Bshl)")
		CASE(Shr, "Bshr")
		CASE(ShrAssign, "(Bop_assign Bshr)")
		CASE(Sub, "Bsub")
		CASE(SubAssign, "(Bop_assign Bsub)")
		CASE(Xor, "Bxor")
		CASE(XorAssign, "(Bop_assign Bxor)")
#undef CASE
		default:
		  error() << "defaulting binary operator\n";
		  ctor("Bother") << "\"" <<  def << "\"" << fmt::rparen;
		  break;
	  }
	}

	void
	VisitBinaryOperator (const BinaryOperator *expr) {
	  switch (expr->getOpcode()) {
		case BinaryOperatorKind::BO_Comma:
		  ctor("Ecomma");
		  break;
		case BinaryOperatorKind::BO_LAnd:
		  ctor("Eseqand");
		  break;
		case BinaryOperatorKind::BO_LOr:
		  ctor("Eseqor");
		  break;
		case BinaryOperatorKind::BO_Assign:
		  ctor("Eassign");
		  break;
		default:
		  ctor("Ebinop");
		  printBinaryOperator(expr->getOpcode(), expr->getOpcodeStr());
		  output() << fmt::nbsp;
		  break;
	  }

	  parent->printExpr(expr->getLHS());
	  output() << fmt::nbsp;
	  parent->printExpr(expr->getRHS());
	  output() << fmt::rparen;
	}

	void
	VisitDependentScopeDeclRefExpr(const DependentScopeDeclRefExpr *expr) {
	  ConstStmtVisitor<PrintExpr, void>::VisitDependentScopeDeclRefExpr(expr);
#if 0
	  // todo(gmm): this doesn't work.
	  error() << "DependentScopeDecl"
	  ctor("Edynref");
	  output() << "\"";
	  expr->getQualifier()->dump();
	  output() << expr->getDeclName().getAsString() << "\"";
	  for (auto a : expr->template_arguments()) {
		output() << fmt::nbsp;
		parent->printExpr(a.getArgument().getAsExpr());
	  }
	  output() << fmt::rparen;
#endif
	}

	void
	printUnaryOperator(UnaryOperator::Opcode op) {
	  switch (op) {
#define CASE(k, s) \
		case UnaryOperatorKind::UO_##k: output() << s; break;
		CASE(Minus, "Uminus")
		CASE(Not, "Ubnot")
		CASE(LNot, "Unot")
		CASE(PostDec, "<PostDec>")
		CASE(PostInc, "<PostInc>")
		CASE(PreDec, "<PreDec>")
		CASE(PreInc, "<PreInc>")
#undef CASE
		default:
		  error() << "unsupported unary operator\n";
		  output() << "(Uother \"" << UnaryOperator::getOpcodeStr(op) << "\")";
		  break;
	  }
	}

	void
	VisitUnaryOperator (const UnaryOperator *expr) {
	  switch (expr->getOpcode()) {
		case UnaryOperatorKind::UO_AddrOf:
		  ctor("Eaddrof");
		  break;
		case UnaryOperatorKind::UO_Deref:
		  ctor("Ederef");
		  break;
		case UnaryOperatorKind::UO_PostInc:
		  ctor("Epostinc");
		  break;
		case UnaryOperatorKind::UO_PreInc:
		  ctor("Epreinc");
		  break;
		case UnaryOperatorKind::UO_PostDec:
		  ctor("Epostdec");
		  break;
		case UnaryOperatorKind::UO_PreDec:
		  ctor("Epredec");
		  break;
		default:
		  ctor("Eunop");
		  printUnaryOperator(expr->getOpcode());
		  output() << fmt::nbsp;
	  }
	  parent->printExpr(expr->getSubExpr());
	  output() << fmt::rparen;
	}

	void
	VisitDeclRefExpr (const DeclRefExpr *expr) {
	  ctor("Evar");
	  parent->printName(expr->getDecl());
	  output() << fmt::rparen;
	}

	void
	VisitCallExpr (const CallExpr *expr) {
	  ctor("Ecall");
	  parent->printExpr(expr->getCallee());
	  output() << fmt::nbsp;
	  PRINT_LIST(expr->arg, parent->printExpr)
	  output() << fmt::rparen;
	}

	void
	VisitCastExpr (const CastExpr *expr) {
	  ctor("Ecast");
	  if (expr->getConversionFunction()) {
		ctor("Cuser");
		parent->printGlobalName(expr->getConversionFunction());
		output() << fmt::rparen;
	  } else {
		ctor("CCcast");
		printCastKind(output(), expr->getCastKind());
		output() << fmt::rparen;
	  }

	  output() << fmt::nbsp;
	  parent->printExpr(expr->getSubExpr());
	  output() << fmt::rparen;
	}

	void
	VisitCXXNamedCastExpr(const CXXNamedCastExpr *expr) {
	  ctor("Ecast");
	  if (expr->getConversionFunction()) {
		return VisitCastExpr(expr);
	  }

	  if (isa<CXXReinterpretCastExpr>(expr)) {
		ctor("Creinterpret");
	  } else if (isa<CXXConstCastExpr>(expr)) {
		ctor("Cconst");
		output() << fmt::rparen;
	  } else if (isa<CXXStaticCastExpr>(expr)) {
		ctor("Cstatic");
	  } else if (isa<CXXDynamicCastExpr>(expr)) {
		ctor("Cdynamic");
	  } else {
		error() << "unknown named cast\n";
		llvm::errs().flush();
		assert(false);
	  }
	  parent->printQualType(expr->getType());
	  output() << fmt::rparen << fmt::nbsp;

	  parent->printExpr(expr->getSubExpr());
	  output() << fmt::rparen;
	}

	void
	VisitIntegerLiteral (const IntegerLiteral *lit) {
	  ctor("Eint") << lit->getValue() << fmt::nbsp;
	  parent->printQualType(lit->getType());
	  output() << fmt::rparen;
	}

	void
	VisitCharacterLiteral (const CharacterLiteral *lit) {
	  ctor("Echar") << lit->getValue() << fmt::nbsp;
	  parent->printQualType(lit->getType());
	  output() << fmt::rparen;
	}

	void
	VisitStringLiteral (const StringLiteral *lit) {
	  ctor("Estring") << "\"" << lit->getBytes() << "\"" << fmt::rparen;
	}

	void
	VisitCXXBoolLiteralExpr (const CXXBoolLiteralExpr *lit) {
	  if (lit->getValue()) {
		output() << "(Ebool true)";
	  } else {
		output() << "(Ebool false)";
	  }
	}

	void
	VisitMemberExpr (const MemberExpr *expr) {
	  ctor("Emember");
	  parent->printExpr(expr->getBase());
	  output() << fmt::nbsp;
	  if (FieldDecl* f = dyn_cast<clang::FieldDecl>(expr->getMemberDecl())) {
		output() << "{| f_type :=" << fmt::nbsp;
		parent->printGlobalName(f->getParent());
		output() << fmt::nbsp << "; f_name := \"" << f->getNameAsString() << "\" |}";
	  } else if (CXXMethodDecl* meth = dyn_cast<clang::CXXMethodDecl>(expr->getMemberDecl())) {
		output() << "{| f_type :=" << fmt::nbsp;
		parent->printGlobalName(meth->getParent());
		output() << fmt::nbsp << "; f_name := \"" << meth->getNameAsString() << "\" |}";
	  } else {
		error() << "member not pointing to field " << expr->getMemberDecl()->getDeclKindName() << "\n";
	  }
	  output() << fmt::rparen;
	}

	void
	VisitArraySubscriptExpr (const ArraySubscriptExpr *expr) {
	  ctor("Esubscript");
	  parent->printExpr(expr->getLHS());
	  output() << fmt::nbsp;
	  parent->printExpr(expr->getRHS());
	  output() << fmt::rparen;
	}

	void
	VisitCXXConstructExpr (const CXXConstructExpr *expr) {
	  ctor("Econstructor");
	  parent->printGlobalName(expr->getConstructor());
	  output() << fmt::nbsp;
	  PRINT_LIST(expr->arg, parent->printExpr)
	  output() << fmt::rparen;
	}

	void
	VisitCXXMemberCallExpr (const CXXMemberCallExpr *expr) {
	  auto method = expr->getMethodDecl();
	  ctor("Emember_call");
	  output() << (method->isVirtual() ? "true" : "false") << fmt::nbsp;

	  parent->printGlobalName(method);
	  output() << fmt::nbsp;
	  parent->printExpr(expr->getImplicitObjectArgument());
	  output() << fmt::nbsp;
	  PRINT_LIST(expr->arg, parent->printExpr)
	  output() << fmt::rparen;
	}

	void
	VisitCXXDefaultArgExpr (const CXXDefaultArgExpr *expr) {
	  ctor("Eimplicit");
	  parent->printExpr(expr->getExpr());
	  output() << fmt::rparen;
	}

	void
	VisitConditionalOperator(const ConditionalOperator *expr) {
	  ctor("Eif");
	  parent->printExpr(expr->getCond());
	  output() << fmt::nbsp;
	  parent->printExpr(expr->getTrueExpr());
	  output() << fmt::nbsp;
	  parent->printExpr(expr->getFalseExpr());
	  output() << fmt::rparen;
	}

#if CLANG_VERSION_MAJOR >= 8
	void
	VisitConstantExpr(const ConstantExpr *expr) {
	  this->Visit(expr->getSubExpr());
	}
#endif

	void
	VisitParenExpr(const ParenExpr *e) {
	  this->Visit(e->getSubExpr());
	}

	void
	VisitInitListExpr(const InitListExpr *expr) {
	  ctor("Einitlist") << "[";
	  // I can't use PRINT_LIST here because there is no prefix to `begin` and `end`
	  for (auto i = expr->begin(), e = expr->end(); i != e; ) {
		parent->printExpr(*i);
		if (++i != e) {
		  output() << ";";
		}
	  }
	  output() << "]" << fmt::rparen;
	}

	void
	VisitCXXThisExpr(const CXXThisExpr *expr) {
	  output() << "Ethis";
	}

	void
	VisitCXXNullPtrLiteralExpr(const CXXNullPtrLiteralExpr *expr) {
	  output() << "Enull";
	}

	void
	VisitUnaryExprOrTypeTraitExpr(const UnaryExprOrTypeTraitExpr *expr) {
	  auto do_arg = [this, expr]() {
		if (expr->isArgumentType()) {
		  ctor("inl");
		  parent->printQualType(expr->getArgumentType());
		  output() << fmt::rparen;
		} else if (expr->getArgumentExpr()){
		  ctor("inr");
		  assert(expr->getArgumentExpr());
		  parent->printExpr(expr->getArgumentExpr());
		  output() << fmt::rparen;
		} else {
		  error() << "argument isnt' a type or an expression\n";
		  llvm::errs().flush();
		}
	  };

	  if (expr->getKind() == UnaryExprOrTypeTrait::UETT_AlignOf) {
		output() << fmt::lparen << "Ealign_of" << fmt::nbsp;
		do_arg();
		output() << fmt::rparen;
	  } else if (expr->getKind() == UnaryExprOrTypeTrait::UETT_SizeOf) {
		output() << fmt::lparen << "Esize_of" << fmt::nbsp;
		do_arg();
		output() << fmt::rparen;
	  } else {
		error() << "unsupported expression `UnaryExprOrTypeTraitExpr`\n";
	  }
	}

	void
	VisitSubstNonTypeTemplateParmExpr(const SubstNonTypeTemplateParmExpr *expr) {
	  this->Visit(expr->getReplacement());
	}

	void
	VisitCXXNewExpr(const CXXNewExpr *expr) {
	  ctor("Enew");
	  if (expr->getOperatorNew()) {
		ctor("Some");
		parent->printGlobalName(expr->getOperatorNew());
		output() << fmt::lparen;
	  } else {
		output() << "None";
	  }

	  output() << fmt::nbsp;

	  parent->printExpr(expr->getConstructExpr());

	  output() << fmt::rparen;
	}

	void
	VisitCXXDeleteExpr(const CXXDeleteExpr *expr) {
	  ctor("Edelete");
	  output() << (expr->isArrayForm() ? "true" : "false") << fmt::nbsp;

	  if (expr->getOperatorDelete()) {
		ctor("Some");
		parent->printGlobalName(expr->getOperatorDelete());
		output() << fmt::rparen;
	  } else {
		output() << "None";
	  }
	  output() << fmt::nbsp;

	  parent->printExpr(expr->getArgument());

	  output() << fmt::rparen;
	}

	// todo(gmm): we could probably get around having the next three definitions.

	void
	VisitExprWithCleanups(const ExprWithCleanups *expr) {
	  error() << "[ERR] ExprWithCleanps is not supported, consider changing your code to explicitly allocate the temporary.\n";
	  exit(1);

	  // note(gmm): my intuition is that these are expressions that create temporaries and then
	  // free them.
	  // note(gmm): it doesn't seem like there is any way to determine the number or type of the
	  // temporaries that are constructed just from looking at this node.
	  ctor("Eandclean");
	  parent->printExpr(expr->getSubExpr());
	  output() << fmt::rparen;
	}

	void
	VisitMaterializeTemporaryExpr(const MaterializeTemporaryExpr *expr) {
	  error() << "mangling number = " << expr->getManglingNumber() << "\n";
	  parent->printExpr(expr->GetTemporaryExpr());
	}

	void
	VisitCXXTemporaryObjectExpr(const CXXTemporaryObjectExpr *expr) {
	  ctor("Econstructor");
	  parent->printGlobalName(expr->getConstructor());
	  output() << fmt::nbsp;
	  PRINT_LIST(expr->arg, parent->printExpr)
	  output() << fmt::rparen;
	}
  };

  class PrintDecl : public ConstDeclVisitorArgs<PrintDecl, bool, Filter::What> {
  protected:
  	ToCoq *const parent;

  	DELEGATE_OUTPUT(parent)

  public:
  	PrintDecl(ToCoq *_parent)
	  : parent(_parent) {
	}

	bool
	VisitDecl (const Decl* d, Filter::What what) {
	  error() << "visiting declaration..." << d->getDeclKindName() << "\n";
	  return false;
	}

	bool
	VisitTypeDecl (const TypeDecl* type, Filter::What what) {
	  error() << "unsupported type declaration `" << type->getDeclKindName()
		  << "`\n";
	  return false;
	}

	bool
	VisitEmptyDecl (const EmptyDecl *decl, Filter::What what) {
	  return false;
	}

	bool
	VisitTypedefNameDecl (const TypedefNameDecl* type, Filter::What what) {
	  output() << fmt::lparen << "Dtypedef \"" << type->getNameAsString() << "\"" << fmt::nbsp;
	  parent->printQualType(type->getUnderlyingType());
	  output() << fmt::rparen;
	  return true;
	}

	bool
	VisitCXXRecordDecl (const CXXRecordDecl *decl, Filter::What what) {
	  if (decl != decl->getCanonicalDecl()) {
		return false;
	  }
	  ctor("Dstruct");
	  parent->printGlobalName(decl);
	  output() << fmt::nbsp;
	  if (!decl->isCompleteDefinition()) {
		output() << "None" << fmt::rparen;
		return true;
	  }

	  ctor("Some");

	  // print the base classes
	  output() << fmt::line << "{| s_bases :=" << fmt::nbsp;
	  auto print_base = [this](const CXXBaseSpecifier &base) {
		if (base.isVirtual()) {
		  error() << "virtual base classes not supported\n";
		}

		auto rec = base.getType().getTypePtr()->getAsCXXRecordDecl();
		if (rec) {
		  parent->printGlobalName(rec);
		} else {
		  error() << "base class is not a RecordType";
		}
	  };
	  PRINT_LIST(decl->bases, print_base)

	  // print the fields
	  output() << fmt::line << "; s_fields :=" << fmt::indent << fmt::line;
	  auto print_field = [this](const FieldDecl *field) {
		output() << "(\"" << field->getNameAsString() << "\"," << fmt::nbsp;
		parent->printQualType(field->getType());
		output() << ","  << fmt::nbsp;
		if (const Expr* init = field->getInClassInitializer()) {
		 ctor("Some");
		 parent->printExpr(init);
		 output() << fmt::rparen;
		} else {
		  output() << "None";
		}
		output() << ")";
	  };
	  PRINT_LIST(decl->field, print_field)
	  output() << fmt::outdent;

	  // print the constructors
	  // todo(gmm): check on the semantics of the instructions. in particular, determine the order of constructor initialization.
	  output() << fmt::line << "; s_ctors :=" << fmt::indent << fmt::line;
	  for (auto i = decl->ctor_begin(), e = decl->ctor_end(); i != e; ++i) {
		const CXXConstructorDecl *cd = *i;
		if (cd->isDeleted()) {
		  error() << "[INFO] skipping deleted constructor\n";
		} else {
		  output() << "{| c_params :=" << fmt::nbsp;
		  PRINT_LIST(cd->param, parent->printParam);
		  output() << fmt::line << " ; c_body :=" << fmt::nbsp << fmt::indent << fmt::indent;
		  if (cd->hasBody()) {
			ctor("Some");
			ctor("UserDefined") << fmt::lparen;
			auto print_init = [this](const CXXCtorInitializer* init) {
			  if (init->isMemberInitializer()) {
				output() << fmt::lparen << "Field \"" << init->getMember()->getNameAsString() << "\"," << fmt::nbsp;
				parent->printExpr(init->getInit());
				output() << fmt::rparen;
			  } else if (init->isBaseInitializer()) {
				output() << fmt::lparen << "Base" << fmt::nbsp;
				parent->printGlobalName(init->getBaseClass()->getAsCXXRecordDecl());
			    output() << "," << fmt::nbsp;
				parent->printExpr(init->getInit());
				output() << fmt::rparen;
			  } else {
				error() << "[ERR] unknown base initializer\n";
			  }
			};
			PRINT_LIST(cd->init, print_init)
			output() << "," << fmt::nbsp;
			parent->printStmt(cd->getBody());
			output() << fmt::rparen << fmt::rparen << fmt::rparen;
		  } else if (cd->isDefaulted()) {
			// todo(gmm): i need to figure out how to generate the default constructors
			output() << "(Some Defaulted)";
		  } else {
			output() << "None";
		  }
		  output() << fmt::outdent << fmt::outdent << fmt::nbsp << "|}";
		  output() << "::" << fmt::line;
		}
	  }
	  output() << fmt::outdent << "nil" << fmt::line;

	  // print the destructor
	  output() << fmt::line << "; s_dtor :=" << fmt::nbsp << fmt::indent;
	  if (const CXXDestructorDecl *dd = decl->getDestructor()) {
		if (dd->isDeleted()) {
		  output() << "None";
		} else if (dd->isDefaulted()) {
		  // todo(gmm): I need go generate this.
		  ctor("Some") << "Defaulted" << fmt::rparen;
		} else if (dd->getBody()) {
		  ctor("Some");
		  ctor("UserDefined");
		  parent->printStmt(dd->getBody());
		  output() << fmt::rparen << fmt::rparen;
		} else {
		  error() << "destructor has no body\n";
		  output() << "None";
		}
	  } else {
		ctor("Some") << "Defaulted" << fmt::rparen;
	  }
	  output() << fmt::outdent << fmt::line;

	  // print the methods
	  output() << fmt::line << "; s_nested :=" << fmt::nbsp << fmt::indent << fmt::line;
	  {
		PrintMemberDecl printMemberDecl(this->parent, decl);
		for (auto i = decl->method_begin(), e = decl->method_end(); i != e; ++i) {
		  if (!isa<CXXConstructorDecl>(*i) && !isa<CXXDestructorDecl>(*i)) {
			if (printMemberDecl.Visit(*i, what)) {
			  output() << fmt::line << "::" << fmt::nbsp;
			}
		  }
		}
		output() << "nil" << fmt::outdent;
	  }

	  output() << "|}" << fmt::rparen << fmt::rparen;
	  return true;
	}

	bool
	VisitFunctionDecl (const FunctionDecl *decl, Filter::What what) {
	  ctor("Dfunction");
	  parent->printGlobalName(decl);
	  output() << fmt::nbsp;
	  parent->printFunction(decl, what);
	  output() << fmt::rparen;
	  return true;
	}

	bool
	VisitCXXMethodDecl (const CXXMethodDecl *decl, Filter::What what) {
	  // note(gmm): method bodies are recorded inline in the class, so we don't need
	  // to print them when we are not inside the class.
	  return false;
	}

	bool
	VisitCXXConstructorDecl (const CXXConstructorDecl *decl, Filter::What what) {
	  // note(gmm): i could actually see this if the constructor implementation is in the cpp file, but the
	  // definition is in the hpp file.
	  error() << "seeing a constructor\n";
	  return false;
	}

	bool
	VisitCXXDestructorDecl (const CXXDestructorDecl *decl, Filter::What what) {
	  return false;
	}

	bool
	VisitVarDecl (const VarDecl *decl, Filter::What what) {
	  ctor("Dvar");
	  parent->printGlobalName(decl);
	  output() << fmt::nbsp;
	  parent->printQualType(decl->getType());
	  if (decl->hasInit() && what >= Filter::DEFINITION) {
		output() << fmt::line << fmt::nbsp << fmt::lparen << "Some" << fmt::nbsp;
		parent->printExpr(decl->getInit());
		output() << fmt::rparen;
	  } else {
		output() << "None";
	  }
	  output() << fmt::rparen;
	  return true;
	}

	bool
	VisitUsingDecl (const UsingDecl *decl, Filter::What what) {
	  return false;
	}

	bool
	VisitUsingDirectiveDecl(const UsingDirectiveDecl *decl, Filter::What what) {
	  return false;
	}

	bool
	VisitNamespaceDecl (const NamespaceDecl *decl, Filter::What what) {
	  ctor("Dnamespace") /* << "\"" << decl->getNameAsString() << "\"" */ << fmt::line << fmt::lparen;
	  if (what >= Filter::What::DEFINITION) {
		for (auto d : decl->decls()) {
		  if(parent->printDecl(d)) {
			output() << "::" << fmt::nbsp;
		  }
		}
	  }
	  output() << "nil" << fmt::rparen;
	  output() << fmt::rparen;
	  return true;
	}

	bool
	VisitEnumDecl (const EnumDecl *decl, Filter::What what) {
	  ctor("Denum") << "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;
	  auto t = decl->getIntegerType();
	  if (!t.isNull()) {
		ctor("Some");
		parent->printQualType(decl->getIntegerType());
		output() << fmt::rparen;
	  } else {
		output() << "None";
	  }
	  output() << fmt::nbsp;;

	  auto print_case = [this, what](const EnumConstantDecl *i) {
		output() << fmt::line << "(\"" << i->getNameAsString() << "\",";
		output() << fmt::nbsp;;
		if (auto init = i->getInitExpr()) {
		  if (what >= Filter::What::DEFINITION) {
			output() << "Some" << fmt::nbsp;;
			parent->printExpr(init);
		  }
		} else {
		  output() << "None";
		}
		output() << ")";
	  };

	  PRINT_LIST(decl->enumerator, print_case)

	  output() << fmt::rparen;
	  return true;
	}

	bool
	VisitLinkageSpecDecl (const LinkageSpecDecl *decl, Filter::What what) {
	  // todo(gmm): need to do the language spec
	  ctor("Dextern");
	  PRINT_LIST(decl->decls, parent->printDecl)
	  output() << fmt::rparen;
	  return true;
	}

	bool
	VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl, Filter::What what) {
	  // note(gmm): for now, i am just going to return the specializations.
	  //ctor("Dtemplated");

	  /*
	  output() << "(";
	  for (auto i = decl->getTemplateParameters()->begin(), e = decl->getTemplateParameters()->end(); i != e; ++i) {
		if (auto *nt = dyn_cast<NonTypeTemplateParmDecl>(*i)) {
		  output() << "(NotType" << fmt::nbsp;
		  parent->printQualType(nt->getType());
		  output() << ",\"" << (*i)->getNameAsString() << "\") ::" << fmt::nbsp;
		} else if (isa<TemplateTypeParmDecl>(*i)) {
		  output() << "(Typename, \"" << (*i)->getNameAsString() << "\") ::" << fmt::nbsp;
		} else {
		  error() << "[ERR] unsupported template parameter type " << (*i)->getDeclKindName() << "\n";
		}
	  }
	  output() << "nil)";

	  parent->printDecl(decl->getTemplatedDecl());
	  output() << fmt::nbsp;
	  */

	  if (decl->spec_begin() == decl->spec_end()) {
		return false;
	  }

	  bool first = true;
	  for (auto i : decl->specializations()) {
		if (!first) {
		  output() << "::";
		  first = false;
		}
		parent->printDecl(i);
	  }

	  //PRINT_LIST(decl->spec, parent->printDecl)
	  //output() << fmt::rparen;
	  return true;
	}

	bool
	VisitClassTemplateDecl(const ClassTemplateDecl *decl, Filter::What what) {
	  if (decl->spec_begin() == decl->spec_end()) {
		return false;
	  }

	  bool first = true;
	  for (auto i : decl->specializations()) {
		if (!first) {
		  output() << "::";
		  first = false;
		}
		parent->printDecl(i);
	  }

	  //PRINT_LIST(decl->spec, parent->printDecl)
	  //output() << fmt::rparen;
	  return true;
	}
  };

  class PrintMemberDecl : public ConstDeclVisitorArgs<PrintMemberDecl, bool, Filter::What> {
  protected:
	ToCoq *const parent;

	DELEGATE_OUTPUT(parent)
	const CXXRecordDecl *const record;
  public:
  	PrintMemberDecl(ToCoq *_parent, const CXXRecordDecl *_record)
	  : parent(_parent), record(_record) {
	}

  	bool
	VisitDecl(const Decl *decl, Filter::What what) {
  	  error() << "[ERR] printing member, got type " << decl->getDeclKindName() << "\n";
  	  return false;
  	}

  	bool
	VisitCXXMethodDecl (const CXXMethodDecl *decl, Filter::What what) {
  	  if (decl->isStatic()) {
  		ctor("Dfunction") << "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;
		parent->printFunction(decl, what);
		output() << fmt::rparen;
		return true;
  	  } else {
  		if (decl->isVirtual()) {
  		  error() << "[ERR] virtual functions not supported: " << decl->getNameAsString() << "\n";
  		  return false;
  		}
  		ctor("Dmethod") << "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;
  		parent->printGlobalName(decl->getParent());
  		output() << fmt::nbsp;
		parent->printFunction(decl, what);
		output() << fmt::rparen;
  		return true;
  	  }
	}
  };

private:
  PrintType typePrinter;
  PrintLocalDecl localPrinter;
  PrintParam paramPrinter;
  PrintStmt stmtPrinter;
  PrintExpr exprPrinter;
  PrintDecl declPrinter;
  Filter *const filter;

public:
  explicit
  ToCoq(ASTContext *ctxt, Formatter &fmt, Filter *f)
  : out(fmt), engine(IntrusiveRefCntPtr<DiagnosticIDs>(), IntrusiveRefCntPtr<DiagnosticOptions>()), typePrinter(this), localPrinter(this), paramPrinter(
  		  this), stmtPrinter(this), exprPrinter(this), declPrinter(this), filter(f), Context(ctxt) {
	mangleContext = ItaniumMangleContext::create(*ctxt, engine);

  }

  SourceLocation
  getStartSourceLocWithComment(const Decl* d) {
	if (auto comment = Context->getRawCommentForDeclNoCache(d)) {
	  return comment->getLocStart();
	} else {
	  return d->getLocStart();
	}
  }

  Decl*
  getPreviousDeclInContext(const Decl* d) {
	auto dc = d->getLexicalDeclContext();

	Decl* prev = nullptr;
	for (auto it : dc->decls()) {
	  if (it == d) {
		return prev;
	  } else {
		prev = it;
	  }
	}
	return nullptr;
  }

  SourceLocation
  getPrevSourceLoc(const Decl* d) {
	SourceManager &sm = Context->getSourceManager();
	auto pd = getPreviousDeclInContext(d);
	if (pd && pd->getLocEnd().isValid()) {
	  return pd->getLocEnd();
	} else {
	  return sm.getLocForStartOfFile(sm.getFileID(d->getSourceRange().getBegin()));
	}
  }

  bool
  printDecl (const Decl* d) {
#if 0
	SourceManager &sm = Context->getSourceManager();
	auto start = getPrevSourceLoc(d);
	auto end = getStartSourceLocWithComment(d);
	if (start.isValid() && end.isValid()) {
	  comment::CommentScanner comments(StringRef(sm.getCharacterData(start), sm.getCharacterData(end) - sm.getCharacterData(start)));
	  StringRef comment;
	  while (comments.next(comment)) {
		error() << "comment:\n";
		error() << comment << "\n";
	  }
	}
#endif

	Filter::What what = filter->shouldInclude(d);
	if (what != Filter::What::NOTHING) {
	  return declPrinter.Visit(d, what);
	}
	return false;
  }

  void
  printParam (const ParmVarDecl* d) {
	paramPrinter.Visit(d);
  }

  void
  printLocalDecl (const Decl* d) {
	localPrinter.Visit(d);
  }

  void
  printStmt (const Stmt* s) {
	stmtPrinter.Visit(s);
  }

  void
  printType (const Type* t) {
	typePrinter.Visit(t);
  }

  void
  printExpr (const Stmt* d) {
	exprPrinter.Visit(d);
  }

  void
  printDeclContext(const DeclContext *ctx) {
	std::list<const DeclContext*> ctxs;

	ctxs.push_front(ctx);
	while ( (ctx = ctx->getParent()) ) {
	  ctxs.push_front(ctx);
	}

	// pop the translation unit
	assert(ctxs.front()->getDeclKind() == Decl::Kind::TranslationUnit);
	ctxs.pop_front();

	while(!ctxs.empty()) {
	  const DeclContext *dc = ctxs.front();
	  ctxs.pop_front();

	  assert(dc);

	  if (const auto *ns = dyn_cast<NamespaceDecl>(dc)) {
		output() << "\"" << ns->getNameAsString() << "\"" << fmt::nbsp << "!::" << fmt::nbsp;
	  } else if (const auto *rd = dyn_cast<CXXRecordDecl>(dc)) {
	  	output() << "\"" << rd->getNameAsString() << "\"" << fmt::nbsp << "!::" << fmt::nbsp;;
	  } else if (const auto *crd = dyn_cast<RecordDecl>(dc)) {
		output() << "\"" << crd->getNameAsString() << "\"" << fmt::nbsp << "!::" << fmt::nbsp;;
	  } else if (const auto *ed = dyn_cast<EnumDecl>(dc)) {
		output() << "\"" << ed->getNameAsString() << "\"" << fmt::nbsp << "!::" << fmt::nbsp;;
	  } else if (isa<LinkageSpecDecl>(dc)) {
		// linkage specifications don't have names
		continue;
	  } else if (isa<TranslationUnitDecl>(dc)) {
		assert(false);
	  } else {
		error() << "something unexpected " << dc->getDeclKindName() << "\n";
		return;
	  }
	}

	output() << "NStop";
  }

  void
  printGlobalName(const NamedDecl *decl) {
	assert(!decl->getDeclContext()->isFunctionOrMethod());

	output() << "\"";
	mangleContext->mangleCXXName(decl, out.nobreak());
	output() << "\"";

	// llvm::errs() << "\n";
	// output() << fmt::indent << "{| g_path :=" << fmt::nbsp;
	// printDeclContext(decl->getDeclContext());
	// output() << "; g_name :=" << fmt::nbsp << "\"" << decl->getNameAsString() << "\" |}";
	// output() << fmt::outdent;
  }

  void
  printName(const NamedDecl *decl) {
	if (decl->getDeclContext()->isFunctionOrMethod()) {
	  ctor("Lname");
	  output() << fmt::nbsp << "\"" << decl->getNameAsString() << "\"";
	} else {
	  ctor("Gname");
	  printGlobalName(decl);
	}
	output() << fmt::rparen;
  }

  void
  printQualType(const QualType &qt) {
	if (qt.isLocalConstQualified()) {
	  if (qt.isVolatileQualified()) {
		ctor("Qconst_volatile");
	  } else {
		ctor("Qconst");
	  }
	} else {
	  if (qt.isLocalVolatileQualified()) {
		ctor("Qmut_volatile");
	  } else {
		ctor("Qmut");
	  }
	}
	printType(qt.getTypePtr());
    output() << fmt::rparen;
  }

  void
  printFunction(const FunctionDecl *decl, Filter::What what) {
	output() << "{| f_return :=" << fmt::indent;
	output() << fmt::nbsp;
	printQualType(decl->getCallResultType());
	output() << "; f_params :=" << fmt::nbsp;
	PRINT_LIST(decl->param, printParam);
	output() << "; f_body :=" << fmt::nbsp;
	if (decl->getBody() && what >= Filter::DEFINITION) {
	  output() << fmt::lparen << "Some" << fmt::nbsp;
	  printStmt(decl->getBody());
	  output() << fmt::rparen;
	} else {
	  output() << "None";
	}
	output() << fmt::outdent << "|}";
  }

  void
  translateModule (const TranslationUnitDecl* decl) {
	output() << "Definition module : list Decl :=" << fmt::indent << fmt::line;
	for (auto i = decl->decls_begin(), e = decl->decls_end(); i != e; ++i) {
	  if (printDecl(*i)) {
		output() << fmt::line << "::" << fmt::nbsp;
	  }
	}
	output() << "nil." << fmt::outdent;
	output() << fmt::line;
  }

private:
  ASTContext *Context;
};


void
declToCoq (ASTContext *ctxt, const clang::Decl* decl) {
  Formatter fmt(llvm::outs());
  Default filter(Filter::What::DEFINITION);
  ToCoq(ctxt, fmt, &filter).printDecl(decl);
}


void
stmtToCoq (ASTContext *ctxt, const clang::Stmt* stmt) {
  Formatter fmt(llvm::outs());
  Default filter(Filter::What::DEFINITION);
  ToCoq(ctxt, fmt, &filter).printStmt(stmt);
}

void
toCoqModule(clang::ASTContext *ctxt, const clang::TranslationUnitDecl *decl) {
  NoInclude noInclude(ctxt->getSourceManager());
  FromComment fromComment(ctxt);
  std::list<Filter*> filters;
  filters.push_back(&noInclude);
  filters.push_back(&fromComment);
  Combine<Filter::What::NOTHING, Filter::max> filter(filters);

  Formatter fmt(llvm::outs());

  fmt << "From Cpp Require Import Parser." << fmt::line << fmt::line
      << "Local Open Scope string_scope." << fmt::line
	  << "Import ListNotations." << fmt::line;

  ToCoq(ctxt, fmt, &filter).translateModule(decl);
}

