#include <list>
#include <Formatter.hpp>
#include "clang/Basic/Version.inc"
#include "clang/AST/Type.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/TypeVisitor.h"


using namespace clang;
using namespace fmt;

void
printCastKind (Formatter& out, const CastKind ck) {
  if (ck == CastKind::CK_LValueToRValue) {
	out << "Cl2r";
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
  } else {
#if CLANG_VERSION_MAJOR >= 8
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
 * of their visitors (only to `TypeVisitor`) so instead we have to have a configuration
 * and then maintain pointers to it everywhere.
 */
class ToCoq : public ConstDeclVisitor<ToCoq, void>
{
private:
  Formatter &out;

  DELEGATE_OUTPUT_I(out)

  fmt::Formatter&
  ctor(const char* ctor, bool line=true) {
	if (line) {
	  output() << fmt::line;
	}
	return output() << fmt::lparen << ctor << fmt::nbsp;
  }

  void
  writeDeclContext(const DeclContext *ctx) {
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
	output() << fmt::indent << "{| g_path :=" << fmt::nbsp;
	writeDeclContext(decl->getDeclContext());
	output() << "; g_name :=" << fmt::nbsp << "\"" << decl->getNameAsString() << "\" |}";
	output() << fmt::outdent;
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
	goType(qt.getTypePtr());
    output() << fmt::rparen;
  }

  class PrintType : public TypeVisitor<PrintType, void>
  {
  private:
	ToCoq *parent;

	DELEGATE_OUTPUT(parent)

  public:
	PrintType (ToCoq *_parent)
		: parent(_parent) {
	}

	void
	VisitType (const Type* type) {
	  error() << "Unsupported type: ";
	  type->dump(error());
	  error() << "\n";
	  output() << "(Tunknown \"" << type->getTypeClassName() << "\")";
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
	  } else if (type->getKind() == BuiltinType::Kind::LongLong) {
		output() << "T_longlong";
	  } else if (type->getKind() == BuiltinType::Kind::ULongLong) {
		output() << "T_ulonglong";
	  } else if (type->getKind() == BuiltinType::Kind::Short) {
		output() << "T_short";
	  } else if (type->getKind() == BuiltinType::Kind::Char16) {
		output() << "T_char16";
	  } else if (type->getKind() == BuiltinType::Kind::Char_S) {
		output() << "T_schar";
	  } else if (type->getKind() == BuiltinType::Kind::SChar) {
		output() << "T_schar";
	  } else if (type->getKind() == BuiltinType::Kind::UChar) {
		output() << "T_uchar";
	  } else if (type->getKind() == BuiltinType::Kind::Char_U) {
		output() << "T_uchar";
#if CLANG_VERSION_MAJOR > 7
	  } else if (type->getKind() == BuiltinType::Kind::Char8) {
		output() << "T_char8";
#endif
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
  };

  class PrintLocalDecl : public ConstDeclVisitor<PrintLocalDecl, void>
  {
  private:
	ToCoq *parent;

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
		parent->goExpr(decl->getInit());
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

  class PrintParam : public ConstDeclVisitor<PrintParam, void>
  {
  private:
	ToCoq *parent;

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
	ToCoq *parent;DELEGATE_OUTPUT(parent)
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
	  PRINT_LIST(stmt->decl, parent->goLocalDecl)
	  output() << fmt::rparen;
	}

	void
	VisitWhileStmt (const WhileStmt* stmt) {
	  ctor("Swhile");
	  if (stmt->getConditionVariable()) {
		error() << "unsupported variable declaration in while";
	  }
	  parent->goExpr(stmt->getCond());
	  output() << fmt::nbsp;
	  parent->goStmt(stmt->getBody());
	  output() << fmt::rparen;
	}

	void
	VisitForStmt (const ForStmt* stmt) {
	  ctor("Sfor");
	  OPTIONAL(parent->goStmt, stmt->getInit())
	  output() << fmt::nbsp;
	  OPTIONAL(parent->goExpr, stmt->getCond())
	  output() << fmt::nbsp;
	  OPTIONAL(parent->goExpr, stmt->getInc())
	  output() << fmt::nbsp;
	  parent->goStmt(stmt->getBody());
	  output() << fmt::rparen;
	}

	void
	VisitDoStmt (const DoStmt* stmt) {
	  ctor("Sdo");
	  parent->goStmt(stmt->getBody());
	  output() << fmt::nbsp;
	  parent->goStmt(stmt->getCond());
	  output() << fmt::rparen;
	}

	void
	VisitIfStmt (const IfStmt* stmt) {
	  ctor("Sif");
	  if (stmt->getConditionVariable()) {
		ctor("Some");
		parent->goLocalDecl(stmt->getConditionVariable());
		output() << fmt::rparen;
	  } else {
		output() << "None";
	  }
	  output() << fmt::nbsp;
	  parent->goExpr(stmt->getCond());
	  output() << fmt::nbsp;
	  parent->goStmt(stmt->getThen());
	  output() << fmt::nbsp;
	  if (stmt->getElse()) {
		parent->goStmt(stmt->getElse());
	  } else {
		output() << "Sskip";
	  }
	  output() << fmt::rparen;
	}

	void
	VisitExpr (const Expr *expr) {
	  ctor("Sexpr");
	  parent->goExpr(expr);
	  output() << fmt::rparen;
	}

	void
	VisitReturnStmt (const ReturnStmt *stmt) {
	  if (stmt->getRetValue() != nullptr) {
		ctor("Sreturn (Some");
		parent->goExpr(stmt->getRetValue());
		output() << ")" << fmt::rparen;
	  } else {
		output() << "(Sreturn None)";
	  }
	}

	void
	VisitCompoundStmt (const CompoundStmt *stmt) {
	  ctor("Sseq");
	  PRINT_LIST(stmt->body, parent->goStmt)
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
	ToCoq *parent;DELEGATE_OUTPUT(parent)
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
	VisitBinaryOperator (const BinaryOperator *expr) {
	  ctor("Ebinop");
	  output() << "\"" << expr->getOpcodeStr() << "\"" << fmt::nbsp;
	  parent->goExpr(expr->getLHS());
	  output() << fmt::nbsp;
	  parent->goExpr(expr->getRHS());
	  output() << fmt::rparen;
	}

	void
	VisitUnaryOperator (const UnaryOperator *expr) {
	  ctor("Eunop") << "\"" << UnaryOperator::getOpcodeStr(expr->getOpcode()) << "\""
		            << fmt::nbsp;
	  parent->goExpr(expr->getSubExpr());
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
	  parent->goExpr(expr->getCallee());
	  output() << fmt::nbsp;
	  PRINT_LIST(expr->arg, parent->goExpr)
	  output() << fmt::rparen;
	}

	void
	VisitCastExpr (const CastExpr *expr) {
	  ctor("Ecast");
	  printCastKind(output(), expr->getCastKind());
	  output() << fmt::nbsp;
	  parent->goExpr(expr->getSubExpr());
	  output() << fmt::rparen;
	}

	void
	VisitIntegerLiteral (const IntegerLiteral *lit) {
	  ctor("Eint") << lit->getValue() << fmt::nbsp;
	  parent->printQualType(lit->getType());
	  output() << fmt::rparen;
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
	  parent->goExpr(expr->getBase());
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
	  parent->goExpr(expr->getLHS());
	  output() << fmt::nbsp;
	  parent->goExpr(expr->getRHS());
	  output() << fmt::rparen;
	}

	void
	VisitCXXConstructExpr (const CXXConstructExpr *expr) {
	  ctor("Econstructor");
	  parent->printGlobalName(expr->getConstructor());
	  output() << fmt::nbsp;
	  PRINT_LIST(expr->arg, parent->goExpr)
	  output() << fmt::rparen;
	}

	void
	VisitCXXMemberCallExpr (const CXXMemberCallExpr *expr) {
	  output() << fmt::line << fmt::lparen << "Emember_call" << fmt::nbsp;
	  parent->printGlobalName(expr->getMethodDecl());
	  output() << fmt::nbsp;
	  parent->goExpr(expr->getImplicitObjectArgument());
	  output() << fmt::nbsp;
	  PRINT_LIST(expr->arg, parent->goExpr)
	  output() << fmt::rparen;
	}

	void
	VisitCXXDefaultArgExpr (const CXXDefaultArgExpr *expr) {
	  ctor("Eimplicit");
	  parent->goExpr(expr->getExpr());
	  output() << fmt::rparen;
	}

	void
	VisitConditionalOperator(const ConditionalOperator *expr) {
	  ctor("Eif");
	  parent->goExpr(expr->getCond());
	  output() << fmt::nbsp;
	  parent->goExpr(expr->getTrueExpr());
	  output() << fmt::nbsp;
	  parent->goExpr(expr->getFalseExpr());
	  output() << fmt::rparen;
	}

#if CLANG_VERSION_MAJOR >= 7
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
		parent->goExpr(*i);
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
		  parent->goType(expr->getArgumentType().getTypePtr()); // constness isn't relevant here
		  output() << fmt::rparen;
		} else {
		  ctor("inr");
		  parent->goExpr(expr->getArgumentExpr());
		  output() << fmt::rparen;
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
  };

private:
  PrintType printType;
  PrintLocalDecl printLocalDecl;
  PrintParam printParam;
  PrintStmt printStmt;
  PrintExpr printExpr;

public:
  explicit
  ToCoq(ASTContext *ctxt, Formatter &fmt)
  : out(fmt), printType(this), printLocalDecl(this), printParam(
  		  this), printStmt(this), printExpr(this), Context(ctxt) { }

  void
  goDecl (const Decl* d) {
	ConstDeclVisitor<ToCoq, void>::Visit(d);
  }

  void
  goLocalDecl (const Decl* d) {
	printLocalDecl.Visit(d);
  }

  void
  goStmt (const Stmt* s) {
	printStmt.Visit(s);
  }

  void
  goType (const Type* t) {
	printType.Visit(t);
  }

  void
  goExpr (const Stmt* d) {
	printExpr.Visit(d);
  }

  // Visiting declarations
  void
  VisitDecl (const Decl* d) {
	error() << "visiting declaration..." << d->getDeclKindName() << "\n";
  }

  void
  VisitTranslationUnitDecl (const TranslationUnitDecl* decl) {
	output() << "Definition module : list Decl :=" << fmt::nbsp;
	PRINT_LIST(decl->decls, goDecl)
	output() << "." << fmt::line;
  }

  void
  VisitTypeDecl (const TypeDecl* type) {
	error() << "unsupported type declaration `" << type->getDeclKindName()
		<< "`\n";
	output() << "Tunknown";
  }

  void
  VisitEmptyDecl (const EmptyDecl *decl) {
	output() << "Dempty";
  }

  void
  VisitTypedefNameDecl (const TypedefNameDecl* type) {
	output() << fmt::lparen << "Dtypedef \"" << type->getNameAsString() << "\"" << fmt::nbsp;
	printQualType(type->getUnderlyingType()); // note(gmm): uses of `getTypePtr` are ignoring modifiers such as `const`
	output() << fmt::rparen;
  }

  void
  VisitCXXRecordDecl (const CXXRecordDecl *decl) {
	if (decl != decl->getCanonicalDecl())
	  return;

	ctor("Dstruct") << "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;

	// print the base classes
	auto print_base = [this](const CXXBaseSpecifier &base) {
	  if (base.isVirtual()) {
		error() << "virtual base classes not supported\n";
	  }
	  auto rec = dyn_cast<RecordType>(base.getType().getTypePtr());
	  if (rec) {
		this->printGlobalName(rec->getDecl());
	  } else {
		error() << "base class is not a RecordType";
	  }
	};
	PRINT_LIST(decl->bases, print_base)

	output() << fmt::nbsp;
	// print the fields
	auto print_field = [this](const FieldDecl *field) {
	  output() << "(\"" << field->getNameAsString() << "\"," << fmt::nbsp;
	  printQualType(field->getType());
	  output() << ")";
	};
	PRINT_LIST(decl->field, print_field)
	output() << fmt::nbsp;

	// print the methods
	auto print_method = [this](const CXXMethodDecl *decl) {
	  // todo(gmm): this is probably wrong because of subtyping. we need to handle constructors
	  // and destructors separately.
	  goDecl(decl);
	};
	PRINT_LIST(decl->method, print_method)

	output() << fmt::rparen;
  }

  void
  printFunction(const FunctionDecl *decl) {
	PRINT_LIST(decl->param, printParam.Visit);
	output() << fmt::nbsp;
	printQualType(decl->getCallResultType());
	output() << fmt::nbsp;
	if (decl->getBody()) {
	  output() << fmt::lparen << "Some" << fmt::nbsp;
	  goStmt(decl->getBody());
	  output() << fmt::rparen;
	} else {
	  output() << "None";
	}
  }

  void
  VisitFunctionDecl (const FunctionDecl *decl) {
	output() << fmt::line << fmt::lparen << "Dfunction \"" << decl->getNameAsString() << "\"" << fmt::nbsp;
	printFunction(decl);
	output() << fmt::rparen;
  }

  void
  VisitCXXMethodDecl (const CXXMethodDecl *decl) {
	this->VisitFunctionDecl(decl);
  }

  void
  VisitCXXConstructorDecl (const CXXConstructorDecl *decl) {
	output() << fmt::line << fmt::lparen << "Dconstructor" << fmt::nbsp;
	PRINT_LIST(decl->param, printParam.Visit);
	output() << fmt::nbsp;
	if (decl->getBody()) {
	  output() << fmt::lparen << "Some" << fmt::nbsp;
	  goStmt(decl->getBody());
	  output() << fmt::rparen;
	} else {
	  output() << "None";
	}
	output() << fmt::rparen;
  }

  void
  VisitCXXDestructorDecl (const CXXDestructorDecl *decl) {
  	output() << fmt::line << fmt::lparen << "Ddestructor" << fmt::nbsp;
	if (decl->getBody()) {
	  output() << fmt::lparen << "Some" << fmt::nbsp;
	  goStmt(decl->getBody());
	  output() << fmt::rparen;
	} else {
	  output() << "None";
	}
  	output() << fmt::rparen;
  }

  void
  VisitVarDecl (const VarDecl *decl) {
	ctor("Dvar") << "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;
	printQualType(decl->getType());
	if (decl->hasInit()) {
	  output() << fmt::line << fmt::nbsp << fmt::lparen << "Some" << fmt::nbsp;
	  goExpr(decl->getInit());
	  output() << fmt::rparen;
	} else {
	  output() << "None";
	}
	output() << fmt::rparen;
  }

  void
  VisitUsingDecl (const UsingDecl *decl) {
	output() << "Dempty"; // note(gmm): this is an artifact because of the way that lists work
  }

  void
  VisitUsingDirectiveDecl(const UsingDirectiveDecl *decl) {
	output() << "Dempty";
  }

  void
  VisitNamespaceDecl (const NamespaceDecl *decl) {
	ctor("Dnamespace") << fmt::nbsp << "\"" << decl->getNameAsString() << "\" ";
	PRINT_LIST(decl->decls, goDecl)
	output() << fmt::rparen;
  }

  void
  VisitEnumDecl (const EnumDecl *decl) {
	ctor("Denum") << "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;
	auto t = decl->getIntegerType();
	if (!t.isNull()) {
	  ctor("Some");
	  printQualType(decl->getIntegerType());
	  output() << fmt::rparen;
	} else {
	  output() << "None";
	}
	output() << fmt::nbsp;;

	auto print_case = [this](const EnumConstantDecl *i) {
	  output() << fmt::line << "(\"" << i->getNameAsString() << "\",";
	  output() << fmt::nbsp;;
	  if (auto init = i->getInitExpr()) {
		output() << "Some" << fmt::nbsp;;
		goExpr(init);
	  } else {
		output() << "None";
	  }
	  output() << ")";
	};

	PRINT_LIST(decl->enumerator, print_case)

	output() << fmt::rparen;
  }

  void
  VisitLinkageSpecDecl (const LinkageSpecDecl *decl) {
	// todo(gmm): need to do the language spec
	ctor("Dextern");
	PRINT_LIST(decl->decls, goDecl)
	output() << fmt::rparen;
  }

  void
  VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl) {
	// note(gmm): for now, i am just going to return the type of the specializations.
	ctor("Dtemplate_function");

	PRINT_LIST(decl->spec, goDecl)

	output() << fmt::rparen;
  }

private:
  ASTContext *Context;
};


void
declToCoq (ASTContext *ctxt, const clang::Decl* decl) {
  Formatter fmt(llvm::outs());
  ToCoq(ctxt, fmt).goDecl(decl);
}


void
stmtToCoq (ASTContext *ctxt, const clang::Stmt* stmt) {
  Formatter fmt(llvm::outs());
  ToCoq(ctxt, fmt).goStmt(stmt);
}

void toCoqModule(clang::ASTContext *ctxt, const clang::TranslationUnitDecl *decl) {
  Formatter fmt(llvm::outs());

  fmt << "From Cpp Require Import Parser." << fmt::line << fmt::line
      << "Local Open Scope string_scope." << fmt::line
	  << "Import ListNotations." << fmt::line;

  ToCoq(ctxt, fmt).goDecl(decl);
}

