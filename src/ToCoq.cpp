#include "clang/AST/Type.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/TypeVisitor.h"

using namespace clang;

class Outputter;

class Outputter
{
private:
  unsigned int depth;

public:
  explicit
  Outputter ()
	  : depth(0) {
  }

  llvm::raw_ostream&
  line () const {
	llvm::outs() << "\n";
	unsigned int d = this->depth;
	while (d--) {
	  llvm::outs() << " ";
	}
	return llvm::outs();
  }

  llvm::raw_ostream&
  nobreak () const {
	return llvm::outs();
  }

  void
  indent () {
	this->depth += 2;
  }
  void
  outdent () {
	this->depth -= 2;
  }

public:
  static Outputter outs;
};

Outputter Outputter::outs = Outputter();

void
printCastKind (llvm::raw_ostream& out, const CastKind ck) {
  if (ck == CastKind::CK_LValueToRValue) {
	out << "Cl2r";
  } else if (ck == CastKind::CK_FunctionToPointerDecay) {
	out << "Cfunction2pointer";
  } else {
	llvm::errs() << "unsupported cast kind \"" << CastExpr::getCastKindName(ck)
		<< "\"";
	out << "Cunsupported";
  }
}

#define DELEGATE_OUTPUT(parent) \
  void indent () { parent->indent (); } \
  void outdent () { parent->outdent (); } \
  llvm::raw_ostream& line () const { return parent->line (); } \
  llvm::raw_ostream& nobreak() const { return parent->nobreak (); } \
  llvm::raw_ostream& error () const { return parent->error(); }

class ToCoq : public ConstDeclVisitor<ToCoq, void>
{
private:
  Outputter* out;

  void
  indent () {
	out->indent();
  }
  void
  outdent () {
	out->outdent();
  }

  llvm::raw_ostream&
  line () const {
	return out->line();
  }

  llvm::raw_ostream&
  nobreak () const {
	return out->nobreak();
  }

  llvm::raw_ostream&
  error () const {
	return llvm::errs();
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
	  nobreak() << "Tunknown";
	}
	void
	VisitBuiltinType (const BuiltinType* type) {
	  if (type->getKind() == BuiltinType::Kind::Bool) {
		nobreak() << "Tbool";
	  } else if (type->getKind() == BuiltinType::Kind::Int128) {
		nobreak() << "(Tint (Some 128) true)";
	  } else if (type->getKind() == BuiltinType::Kind::UInt128) {
		nobreak() << "(Tint (Some 128) false)";
	  } else if (type->getKind() == BuiltinType::Kind::Int) {
		nobreak() << "(Tint None true)";
	  } else if (type->getKind() == BuiltinType::Kind::Char16) {
		nobreak() << "(Tchar (Some 16) true)";
	  } else if (type->getKind() == BuiltinType::Kind::Char_S) {
		nobreak() << "(Tchar None true)";
	  } else if (type->getKind() == BuiltinType::Kind::Char_U) {
		nobreak() << "(Tchar None false)";
	  } else if (type->getKind() == BuiltinType::Kind::Char8) {
		nobreak() << "(Tchar (Some 8) false)";
	  } else if (type->getKind() == BuiltinType::Kind::Char32) {
		nobreak() << "(Tchar (Some 32) false)";
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
		for (DeclGroupRef::const_iterator i = decl->decl_begin(), e =
			decl->decl_end(); i != e; ++i) {
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
	  parent->goStmt(stmt->getElse());
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
	  line() << "(Sseq [";
	  indent();
	  for (CompoundStmt::const_body_iterator I = stmt->body_begin(), E =
		  stmt->body_end(); I != E; ++I) {
		if (I != stmt->body_begin()) {
		  line() << "; ";
		}
		parent->goStmt(*I);
	  }
	  nobreak() << "])";
	  outdent();
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
	VisitBinaryOperator (const BinaryOperator *expr) {
	  line() << "(Ebinop \"" << expr->getOpcodeStr() << "\"";
	  indent();
	  parent->goExpr(expr->getLHS());
	  parent->goExpr(expr->getRHS());
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
	  nobreak() << " [";
	  indent();
	  for (CallExpr::const_arg_iterator i = expr->arg_begin(), e =
		  expr->arg_end(); i != e; ++i) {
		parent->goExpr(*i);
	  }
	  outdent();
	  nobreak() << "])";
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
	  : out(&Outputter::outs), printType(this), printLocalDecl(this), printParam(
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
	line() << "Definition module : list Decl := [";
	indent();
	for (auto i = decl->decls_begin(), e = decl->decls_end(); i != e;) {
	  goDecl(*i);
	  if (++i != e) {
		nobreak() << ";";
	  }
	}
	nobreak() << "].\n";
	outdent();
  }

  void
  VisitTypeDecl (const TypeDecl* type) {
	error() << "unsupported type declaration `" << type->getDeclKindName()
		<< "`\n";
	nobreak() << "Tunknown";
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
	  error() << "base classes no supported\n";
	}

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

private:
  ASTContext *Context;

};

Outputter* defaultOutput = &Outputter::outs;

void
declToCoq (ASTContext *ctxt, const clang::Decl* decl) {
  ToCoq(ctxt).goDecl(decl);
}

void
stmtToCoq (ASTContext *ctxt, const clang::Stmt* stmt) {
  ToCoq(ctxt).goStmt(stmt);
}

