#include <assert.h>
#include "clang/AST/Type.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/TypeVisitor.h"

using namespace clang;

class Outputter;

#if 0
struct NBSP {};

NBSP
nbsp() { return NBSP(); }
#endif

class Outputter
{
private:
  unsigned int depth;
  unsigned int spaces;

public:
  explicit
  Outputter ()
	  : depth(0), spaces(0) {
  }

  llvm::raw_ostream&
  line () {
	llvm::outs() << "\n";
	unsigned int d = this->depth;
	while (d--) {
	  llvm::outs() << " ";
	}
	spaces = 0;
	return llvm::outs();
  }

  llvm::raw_ostream&
  nobreak () {
	while (spaces > 0) {
	  llvm::outs() << " ";
	  spaces--;
	}
	return llvm::outs();
  }

  void
  nbsp () {
	spaces++;
  }

  void
  indent () {
	this->depth += 2;
  }
  void
  outdent () {
	assert(this->depth >= 2);
	this->depth -= 2;
  }

  llvm::raw_ostream&
  error () const {
	return llvm::errs();
  }

public:
  static Outputter default_output;
};

Outputter Outputter::default_output = Outputter();

void
printCastKind (llvm::raw_ostream& out, const CastKind ck) {
  if (ck == CastKind::CK_LValueToRValue) {
	out << "Cl2r";
  } else if (ck == CastKind::CK_FunctionToPointerDecay) {
	out << "Cfunction2pointer";
  } else if (ck == CastKind::CK_NoOp) {
	out << "Cnoop";
  } else if (ck == CastKind::CK_IntegralCast) {
	out << "Cintegral";
  } else if (ck == CastKind::CK_PointerToIntegral) {
	out << "Cpointer2int";
  } else if (ck == CastKind::CK_ArrayToPointerDecay) {
	out << "Carray2pointer";
  } else if (ck == CastKind::CK_ConstructorConversion) {
  	out << "Cconstructorconversion";
  } else if (ck == CastKind::CK_BuiltinFnToFnPtr) {
  	out << "Cbulitin2function";
  } else {
	llvm::errs() << "unsupported cast kind \"" << CastExpr::getCastKindName(ck)
		<< "\"\n";
	out << "Cunsupported";
  }
}

#define DELEGATE_OUTPUT(parent) \
  void indent () { parent->indent (); } \
  void outdent () { parent->outdent (); } \
  void nbsp() { parent->nbsp(); } \
  llvm::raw_ostream& line () const { return parent->line (); } \
  llvm::raw_ostream& nobreak() const { return parent->nobreak (); } \
  llvm::raw_ostream& error () const { return parent->error(); }

#define PRINT_LIST(iterator, fn) \
	nobreak() << "["; \
	indent(); \
    for (auto i = iterator##_begin(), e = iterator##_end(); i != e; ) { \
	  fn(*i); \
	  if (++i != e) { \
	      nobreak() << ";"; \
	  } \
    } \
	outdent(); \
    nobreak() << "]";

class ToCoq : public ConstDeclVisitor<ToCoq, void>
{
private:
  Outputter* out;

  DELEGATE_OUTPUT(out)

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
	  nobreak() << "Tunknown";
	}

	void
	VisitEnumType (const EnumType* type) {
	  parent->nobreak() << "(Talias \"" << type->getDecl()->getNameAsString()
		  << "\")";
	}

	void
	VisitParenType (const ParenType* type) {
	  this->Visit(type->getInnerType().getTypePtr());
	}

	void
	VisitRecordType (const RecordType *type) {
	  parent->nobreak() << "(Talias \"" << type->getDecl()->getNameAsString()
		  << "\")";
	}

	void
	VisitBuiltinType (const BuiltinType* type) {
	  if (type->getKind() == BuiltinType::Kind::Bool) {
		nobreak() << "Tbool";
	  } else if (type->getKind() == BuiltinType::Kind::Int128) {
		nobreak() << "T_int128";
	  } else if (type->getKind() == BuiltinType::Kind::UInt128) {
		nobreak() << "T_uint128";
	  } else if (type->getKind() == BuiltinType::Kind::Int) {
		nobreak() << "T_int";
	  } else if (type->getKind() == BuiltinType::Kind::UInt) {
		nobreak() << "T_uint";
	  } else if (type->getKind() == BuiltinType::Kind::ULong) {
		nobreak() << "T_ulong";
	  } else if (type->getKind() == BuiltinType::Kind::UShort) {
		nobreak() << "T_ushort";
	  } else if (type->getKind() == BuiltinType::Kind::LongLong) {
		nobreak() << "T_longlong";
	  } else if (type->getKind() == BuiltinType::Kind::ULongLong) {
		nobreak() << "T_ulonglong";
	  } else if (type->getKind() == BuiltinType::Kind::Short) {
		nobreak() << "T_short";
	  } else if (type->getKind() == BuiltinType::Kind::Char16) {
		nobreak() << "T_char16";
	  } else if (type->getKind() == BuiltinType::Kind::Char_S) {
		nobreak() << "T_schar";
	  } else if (type->getKind() == BuiltinType::Kind::SChar) {
		nobreak() << "T_schar";
	  } else if (type->getKind() == BuiltinType::Kind::UChar) {
		nobreak() << "T_uchar";
	  } else if (type->getKind() == BuiltinType::Kind::Char_U) {
		nobreak() << "T_uchar";
	  } else if (type->getKind() == BuiltinType::Kind::Char8) {
		nobreak() << "T_char8";
	  } else if (type->getKind() == BuiltinType::Kind::Char32) {
		nobreak() << "T_char32";
	  } else if (type->getKind() == BuiltinType::Kind::Void) {
		nobreak() << "Tvoid";
	  } else {
		error() << "Unsupported type \""
			<< type->getNameAsCString(PrintingPolicy(LangOptions())) << "\"\n";
		nobreak() << "Tunknown";
	  }
	}

	void
	VisitReferenceType (const ReferenceType* type) {
	  parent->line() << "(Treference ";
	  parent->goType(type->getPointeeType().getTypePtr());
	  parent->nobreak() << ")";
	}

	void
	VisitPointerType (const PointerType* type) {
	  parent->line() << "(Tpointer ";
	  parent->goType(type->getPointeeType().getTypePtr());
	  parent->nobreak() << ")";
	}

	void
	VisitTypedefType (const TypedefType *type) {
	  parent->nobreak() << "(Talias \"" << type->getDecl()->getNameAsString()
		  << "\")";
	}

	void
	VisitFunctionProtoType (const FunctionProtoType *type) {
	  parent->line() << "(Tfunction ";
	  parent->goType(type->getReturnType().getTypePtr());
	  parent->nobreak() << " [";
	  parent->indent();
	  for (auto i = type->param_type_begin(), e = type->param_type_end();
		  i != e;) {
		parent->goType((*i).getTypePtr());
		if (++i != e) {
		  parent->nobreak() << "; ";
		}
	  }
	  parent->nobreak() << "])";
	  parent->outdent();
	}

	void
	VisitElaboratedType(const ElaboratedType *type) {
	  this->Visit(type->getNamedType().getTypePtr());
	}

	void
	VisitConstantArrayType(const ConstantArrayType *type) {
	  line() << "(Tarray";
	  nbsp();
	  parent->goType(type->getElementType().getTypePtr());
	  nbsp();
	  nobreak() << "(Some " << type->getSize().getLimitedValue() << "))";
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
	  line() << "(\"" << decl->getNameAsString() << "\", ";
	  indent();
	  parent->goType(decl->getType().getTypePtr());
	  nobreak() << ", ";
	  if (decl->hasInit()) {
		line() << " (Some ";
		parent->goExpr(decl->getInit());
		nobreak() << ")";
	  } else {
		nobreak() << " None";
	  }
	  nobreak() << ")";
	  outdent();
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
	  line() << "(\"" << decl->getNameAsString() << "\", ";
	  indent();
	  parent->goType(decl->getType().getTypePtr());
	  nobreak() << ")";
	  outdent();
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
	VisitDeclStmt (const DeclStmt* decl) {
	  line() << "(Sdecl [";
	  if (decl->isSingleDecl()) {
		indent();
		parent->goLocalDecl(decl->getSingleDecl());
		outdent();
		nobreak() << "]";
	  } else {
		indent();
		for (auto i = decl->decl_begin(), e = decl->decl_end(); i != e; ++i) {
		  parent->goLocalDecl(*i);
		}
		outdent();
	  }
	  nobreak() << ")";
	}

	void
	VisitWhileStmt (const WhileStmt* stmt) {
	  line() << "(Swhile ";
	  indent();
	  if (stmt->getConditionVariable()) {
		error() << "unsupported variable declaration in while";
	  } else {
		nobreak() << "None ";
	  }
	  parent->goStmt(stmt->getCond());
	  parent->goStmt(stmt->getBody());
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitDoStmt (const DoStmt* stmt) {
	  line() << "(Sdo ";
	  indent();
	  parent->goStmt(stmt->getBody());
	  parent->goStmt(stmt->getCond());
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitIfStmt (const IfStmt* stmt) {
	  line() << "(Sif ";
	  indent();
	  if (stmt->getConditionVariable()) {
		line() << "(Some ";
		parent->goDecl(stmt->getConditionVariable());
		nobreak() << ")";
	  } else {
		line() << "None";
	  }
	  parent->goStmt(stmt->getCond());
	  parent->goStmt(stmt->getThen());
	  if (stmt->getElse()) {
		parent->goStmt(stmt->getElse());
	  } else {
		nobreak() << "Sskip";
	  }
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitExpr (const Expr *expr) {
	  line() << "(Sexpr ";
	  indent();
	  parent->goExpr(expr);
	  outdent();
	  nobreak() << ")";
	}

	void
	VisitReturnStmt (const ReturnStmt *stmt) {
	  if (stmt->getRetValue() != nullptr) {
		line() << "(Sreturn (Some ";
		indent();
		parent->goExpr(stmt->getRetValue());
		nobreak() << "))";
		outdent();
	  } else {
		nobreak() << "(Sreturn None)";
	  }
	}

	void
	VisitCompoundStmt (const CompoundStmt *stmt) {
	  line() << "(Sseq ";
	  PRINT_LIST(stmt->body, parent->goStmt)
	  nobreak() << ")";
	}

	void
	VisitNullStmt (const NullStmt *stmt) {
	  line() << "Sskip";
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
	  line() << "(Ebinop \"" << expr->getOpcodeStr() << "\"";
	  indent();
	  parent->goExpr(expr->getLHS());
	  parent->goExpr(expr->getRHS());
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitUnaryOperator (const UnaryOperator *expr) {
	  line() << "(Eunop \"" << UnaryOperator::getOpcodeStr(expr->getOpcode())
		  << "\"";
	  indent();
	  parent->goExpr(expr->getSubExpr());
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitDeclRefExpr (const DeclRefExpr *expr) {
	  line() << "(Evar \"" << expr->getDecl()->getNameAsString() << "\")";
	}

	void
	VisitCallExpr (const CallExpr *expr) {
	  line() << "(Ecall";
	  indent();
	  parent->goExpr(expr->getCallee());
	  nbsp();
	  PRINT_LIST(expr->arg, parent->goExpr)
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitCastExpr (const CastExpr *expr) {
	  line() << "(Ecast ";
	  printCastKind(nobreak(), expr->getCastKind());
	  nobreak() << " ";
	  indent();
	  parent->goExpr(expr->getSubExpr());
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitIntegerLiteral (const IntegerLiteral *lit) {
	  line() << "(Eint " << lit->getValue() << " ";
	  parent->goType(lit->getType().getTypePtr());
	  nobreak() << ")";
	}

	void
	VisitCXXBoolLiteralExpr (const CXXBoolLiteralExpr *lit) {
	  if (lit->getValue()) {
		nobreak() << "(Ebool true)";
	  } else {
		nobreak() << "(Ebool false)";
	  }
	}

	void
	VisitMemberExpr (const MemberExpr *expr) {
	  line() << "(Emember ";
	  indent();
	  parent->goExpr(expr->getBase());
	  nobreak() << " ";
	  if (FieldDecl* f = dyn_cast<clang::FieldDecl>(expr->getMemberDecl())) {
		line() << "\"" << f->getNameAsString() << "\"";
	  } else {
		error() << "member not pointing to field";
	  }
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitArraySubscriptExpr (const ArraySubscriptExpr *expr) {
	  line() << "(Esubscript ";
	  indent();
	  parent->goExpr(expr->getLHS());
	  nobreak() << " ";
	  parent->goExpr(expr->getRHS());
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitCXXConstructExpr (const CXXConstructExpr *expr) {
	  line() << "(Econstructor ";
	  indent();
	  nobreak() << "\"" << expr->getConstructor()->getParent()->getNameAsString() << "\"";
	  nbsp();
	  PRINT_LIST(expr->arg, parent->goExpr)
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitCXXDefaultArgExpr (const CXXDefaultArgExpr *expr) {
	  line() << "(Eimplicit ";
	  indent();
	  parent->goExpr(expr->getExpr());
	  nobreak() << ")";
	  outdent();
	}

	void
	VisitConstantExpr(const ConstantExpr *expr) {
	  this->Visit(expr->getSubExpr());
	}

	void
	VisitParenExpr(const ParenExpr *e) {
	  this->Visit(e->getSubExpr());
	}

	void
	VisitInitListExpr(const InitListExpr *expr) {
	  line() << "(Einitlist [";
	  indent();
	  for (auto i = expr->begin(), e = expr->end(); i != e; ) {
		parent->goExpr(*i);
		if (++i != e) {
		  nobreak() << ";";
		}
	  }
	  outdent();
	  nobreak() << "]";
	}

	void
	VisitCXXThisExpr(const CXXThisExpr *expr) {
	  nobreak() << "Ethis";
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
  ToCoq (ASTContext*ctx)
	  : out(&Outputter::default_output), printType(this), printLocalDecl(this), printParam(
		  this), printStmt(this), printExpr(this), Context(ctx) {
  }

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
	line() << "visiting declaration..." << d->getDeclKindName() << "\n";
  }

  void
  VisitTranslationUnitDecl (const TranslationUnitDecl* decl) {
	line() << "Definition module : list Decl :=";
	nbsp();
	PRINT_LIST(decl->decls, goDecl)
	nobreak() << ".";
	line();
  }

  void
  VisitTypeDecl (const TypeDecl* type) {
	error() << "unsupported type declaration `" << type->getDeclKindName()
		<< "`\n";
	nobreak() << "Tunknown";
  }

  void
  VisitEmptyDecl (const EmptyDecl *decl) {
	line() << "Dempty";
  }

  void
  VisitTypedefNameDecl (const TypedefNameDecl* type) {
	line() << "(Dtypedef \"" << type->getNameAsString() << "\" ";
	goType(type->getUnderlyingType().getTypePtr()); // note(gmm): uses of `getTypePtr` are ignoring modifiers such as `const`
	nobreak() << ")";
  }

  void
  VisitCXXRecordDecl (const CXXRecordDecl *decl) {
	if (decl != decl->getCanonicalDecl())
	  return;

	line() << "(Dstruct \"" << decl->getNameAsString() << "\"";

	indent();
	// print the base classes
	if (decl->getNumBases() > 0) {
	  error() << "base classes not supported\n";
	}
#if 0
	auto print_base = [this](const CXXBaseSpecifier &base) {
	  auto rec = dyn_cast<RecordType>(base.getType().getTypePtr());
	  if (rec) {
		nobreak() << "\"" << rec->getDecl()->getNameAsString() << "\"";
	  } else {
		error() << "base class is not a RecordTypd";
	  }
	};
	PRINT_LIST(decl->bases, print_base)
#endif

	// print the fields
	line() << "[";
	for (auto i = decl->field_begin(), e = decl->field_end(); i != e;) {
	  nobreak() << "(\"" << (*i)->getNameAsString() << "\", ";
	  goType((*i)->getType().getTypePtr());
	  nobreak() << ")";
	  if (++i != e) {
		nobreak() << ";";
	  }
	}
	line() << "]";

	// print the methods
#if 0
	auto print_method = [this](const CXXMethodDecl *decl) {
	  // todo(gmm): this is probably wrong because of subtyping. we need to handle constructors
	  // and destructors separately.
	  goDecl(decl);
	};
	PRINT_LIST(decl->method, print_method)
#endif
	if (decl->method_begin() != decl->method_end()) {
	  error() << "methods not supported\n";
	}

	nobreak() << ")";
	outdent();
  }

  void
  VisitFunctionDecl (const FunctionDecl *decl) {
	line() << "(Dfunction \"" << decl->getNameAsString() << "\" [";
	for (auto i = decl->param_begin(), e = decl->param_end(); i != e;) {
	  printParam.Visit(*i);
	  if (++i != e) {
		line() << ";";
	  }
	}
	nobreak() << "] ";
	goType(decl->getCallResultType().getTypePtr());
	nobreak() << " ";
	indent();
	if (decl->getBody()) {
	  nobreak() << "(Some ";
	  goStmt(decl->getBody());
	  nobreak() << ")";
	} else {
	  nobreak() << "None";
	}
	nobreak() << ")";
	outdent();
  }

  void
  VisitVarDecl (const VarDecl *decl) {
	line() << "(Dvar \"" << decl->getNameAsString() << "\" ";
	indent();
	goType(decl->getType().getTypePtr());
	if (decl->hasInit()) {
	  line() << " (Some ";
	  goExpr(decl->getInit());
	  nobreak() << ")";
	} else {
	  nobreak() << " None";
	}
	nobreak() << ")";
	outdent();
  }

  void
  VisitUsingDecl (const UsingDecl *decl) {
	nobreak() << "Dempty"; // note(gmm): this is an artifact because of the way that lists work
  }

  void
  VisitNamespaceDecl (const NamespaceDecl *decl) {
	line() << "(Dnamespace \"" << decl->getNameAsString() << "\" ";
	PRINT_LIST(decl->decls, goDecl)
	nobreak() << ")";
  }

  void
  VisitEnumDecl (const EnumDecl *decl) {
	line() << "(Denum \"" << decl->getNameAsString() << "\" [";
	nbsp();
	indent();
	if (auto t = decl->getIntegerType().getTypePtr()) {
	  line() << "(Some";
	  nbsp();
	  goType(t);
	  nobreak() << ")";
	} else {
	  nobreak() << "None";
	}
	nbsp();
	nobreak() << "[";
	for (auto i = decl->enumerator_begin(), e = decl->enumerator_end(); i != e; ) {

	  line() << "(\"" << (*i)->getNameAsString() << "\",";
	  nbsp();
	  if (auto init = (*i)->getInitExpr()) {
		nobreak() << "Some";
		nbsp();
		goExpr(init);
	  } else {
		nobreak() << "None";
	  }
	  nobreak() << ")";

	  if (++i != e) {
		nobreak() << ";";
		nbsp();
	  }
	}
	nobreak() << "])";
	outdent();
  }

private:
  ASTContext *Context;
};


Outputter* defaultOutput = &Outputter::default_output;

void
declToCoq (ASTContext *ctxt, const clang::Decl* decl) {
  ToCoq(ctxt).goDecl(decl);
}


void
stmtToCoq (ASTContext *ctxt, const clang::Stmt* stmt) {
  ToCoq(ctxt).goStmt(stmt);
}
