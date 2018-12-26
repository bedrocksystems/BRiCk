//#include "clang/Frontend/CompilerInstance.h"
//#include "clang/Frontend/FrontendAction.h"

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
  Outputter () :
      depth (0)
  {
  }

  llvm::raw_ostream&
  line () const
  {
    llvm::outs () << "\n";
    unsigned int d = this->depth;
    while (d--)
      {
	llvm::outs () << " ";
      }
    return llvm::outs ();
  }

  llvm::raw_ostream&
  nobreak() const {
    return llvm::outs();
  }

  void
  indent ()
  {
    this->depth += 2;
  }
  void
  outdent ()
  {
    this->depth -= 2;
  }

public:
  static Outputter outs;
};

Outputter Outputter::outs = Outputter ();


llvm::raw_ostream&
operator<< (llvm::raw_ostream& out, const CastKind ck)
{
  switch (ck) {
    case CastKind::CK_LValueToRValue:
      out << "Cl2r";
      break;
    case CastKind::CK_FunctionToPointerDecay:
      out << "Cfunction2pointer";
      break;
    default:
      llvm::errs() << "unsupported cast kind \"" << CastExpr::getCastKindName(ck) << "\"";
      out << "Cunsupported";
      break;
  }
  return out;
}

class ToCoq : public ConstStmtVisitor<ToCoq, void>
            , public ConstDeclVisitor<ToCoq, void>
            , public TypeVisitor<ToCoq, void>
{
private:
  Outputter* out;

  void
  indent ()
  {
    out->indent ();
  }
  void
  outdent ()
  {
    out->outdent ();
  }

  llvm::raw_ostream&
  line () const
  {
    return out->line ();
  }

  llvm::raw_ostream&
  nobreak() const
  {
    return out->nobreak ();
  }

  llvm::raw_ostream&
  error () const
  {
    return llvm::errs();
  }
private:
  void
  go (const Stmt *s)
  {
    goStmt (s);
  }
  void
  go (const Decl *s)
  {
    goDecl (s);
  }
  void
  go (const Type* t)
  {
    goType (t);
  }
public:
  explicit
  ToCoq (ASTContext*ctx) :
      out (&Outputter::outs), Context (ctx)
  {
  }

  void
  goDecl (const Decl* d)
  {
    ConstDeclVisitor<ToCoq, void>::Visit (d);
  }
  void
  goStmt (const Stmt* d)
  {
    ConstStmtVisitor<ToCoq, void>::Visit (d);
  }

  void
  goType (const Type* t)
  {
    TypeVisitor<ToCoq, void>::Visit (t);
  }

  // Visiting types
  void
  VisitBuiltinType (const BuiltinType* type)
  {
    line () << type->getNameAsCString (PrintingPolicy (LangOptions ()));
  }

  void
  VisitReferenceType(const ReferenceType* type)
  {
    line() << "(Treference ";
    goType(type->getPointeeType().getTypePtr());
    line() << ")";
  }

  void
  VisitPointerType(const PointerType* type)
  {
    line() << "(Tpointer ";
    goType(type->getPointeeType().getTypePtr());
    line() << ")";
  }

  // Visiting declarations
  void
  VisitDecl (const Decl* d)
  {
    line () << "visiting declaration..." << d->getDeclKindName () << "\n";
  }

  void
  VisitTranslationUnitDecl (const TranslationUnitDecl* decl)
  {
    line () << "translation unit\n";
    for (auto i = decl->decls_begin (), e = decl->decls_end (); i != e; ++i)
      {
	goDecl (*i);
      }
  }

  void
  VisitTypeDecl (const TypeDecl* type)
  {
    line () << "(Dtype \"" << type->getNameAsString () << "\"...)";
  }

  void
  VisitCXXRecordDecl (const CXXRecordDecl *decl)
  {
    if (decl != decl->getCanonicalDecl()) return;

    line() << "(Dstruct \"" << decl->getNameAsString () << "\"";

    indent();
    // print the base classes
    if (decl->getNumBases() > 0) {
	error() << "base classes no supported\n";
    }

    // print the fields
    line() << "[";
    for (auto i = decl->field_begin(), e = decl->field_end(); i != e; ) {
	nobreak() << "(\"" << (*i)->getNameAsString() << "\", ";
	goType((*i)->getType().getTypePtr());
	nobreak() << ")";
	if (++i != e) { line() << ";"; }
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
  VisitFunctionDecl (const FunctionDecl *decl)
  {
    line () << "(Dfunction \"" << decl->getNameAsString () << "\" [p|";
    for (auto i = decl->param_begin (), e = decl->param_end (); i != e;)
      {

	nobreak () << "(\"" << (*i)->getNameAsString () << "\", ";
	goType ((*i)->getType ().getTypePtr ());
	nobreak () << ")";
	if (++i != e)
	  {
	    line () << ";";
	  }
      }
    nobreak() << "|p] ";
    indent ();
    if (decl->getBody()) {
	nobreak() << "(Some ";
	go (decl->getBody ());
	nobreak() << ")";
    } else {
	nobreak() << "None";
    }
    nobreak() << ")";
    outdent ();
  }

  void
  VisitVarDecl (const VarDecl *decl)
  {
    line () << "(Dvar \"" << decl->getNameAsString () << "\" ";
    indent ();
    goType (decl->getType ().getTypePtr ());
    if (decl->hasInit ())
      {
	line () << " (Some ";
	go (decl->getInit ());
	nobreak () << ")";
      }
    else
      {
	nobreak () << " None";
      }
    nobreak() << ")";
    outdent ();
  }

  // Visiting statements
  void
  VisitDeclStmt (const DeclStmt* decl)
  {
    line () << "(Sdeclaration [";
    if (decl->isSingleDecl ())
      {
	indent ();
	go (decl->getSingleDecl ());
	outdent ();
	nobreak () << "]";
      }
    else
      {
	indent ();
	for (DeclGroupRef::const_iterator i = decl->decl_begin (), e =
	    decl->decl_end (); i != e; ++i)
	  {
	    go (*i);
	  }
	outdent ();
      }
    nobreak() << ")";
  }

  void
  VisitWhileStmt(const WhileStmt* stmt)
  {
    line() << "(Swhile ";
    indent();
    if (stmt->getConditionVariable()) {
	line() << "(Some ";
	goDecl(stmt->getConditionVariable());
	nobreak() << ")";
    } else {
	line() << "None";
    }
    goStmt(stmt->getCond());
    goStmt(stmt->getBody());
    nobreak() << ")";
    outdent();
  }

  void
  VisitDoStmt(const DoStmt* stmt)
  {
    line() << "(Sdo ";
    indent();
    goStmt(stmt->getBody());
    goStmt(stmt->getCond());
    nobreak() << ")";
    outdent();
  }

  void
  VisitIfStmt(const IfStmt* stmt)
  {
    line() << "(Sif ";
    indent();
    if (stmt->getConditionVariable()) {
      line() << "(Some ";
      goDecl(stmt->getConditionVariable());
      line() << ")";
    } else {
      line() << "None";
    }
    goStmt(stmt->getCond());
    goStmt(stmt->getThen());
    goStmt(stmt->getElse());
    nobreak() << ")";
    outdent();
  }

  void
  VisitBinaryOperator (const BinaryOperator *expr)
  {
    line () << "(Ebinop \"" << expr->getOpcodeStr () << "\"";
    indent ();
    go (expr->getLHS ());
    go (expr->getRHS ());
    nobreak() << ")";
    outdent ();
  }

  void
  VisitDeclRefExpr (const DeclRefExpr *expr)
  {
    line () << "(Evar \"" << expr->getDecl()->getNameAsString() << "\")";
  }

  void
  VisitCallExpr (const CallExpr *expr)
  {
    line () << "(Ecall";
    indent ();
    go (expr->getCallee ());
    nobreak() << "[e|";
    indent ();
    for (CallExpr::const_arg_iterator i = expr->arg_begin (), e =
	expr->arg_end (); i != e; ++i)
      {
	go (*i);
      }
    outdent ();
    nobreak() << "|e])";
    outdent ();
  }

  void
  VisitCastExpr (const CastExpr *expr)
  {
    line () << "(Ecast " << expr->getCastKind() << " ";
    indent ();
    go (expr->getSubExpr ());
    nobreak() << ")";
    outdent ();
  }

  void
  VisitIntegerLiteral (const IntegerLiteral *lit)
  {
    line () << "(Eint " << lit->getValue () << " ";
    goType (lit->getType ().getTypePtr ());
    nobreak() << ")";
  }

  void
  VisitReturnStmt (const ReturnStmt *stmt)
  {
    if (stmt->getRetValue() != nullptr) {
	line () << "(Sreturn (Some ";
	indent ();
	go (stmt->getRetValue ());
	nobreak() << "))";
	outdent ();
    } else {
	line() << "(Sreturn None)";
    }
  }

  void
  VisitCompoundStmt (const CompoundStmt *stmt)
  {
    line () << "(Sseq [s|";
    indent ();
    for (CompoundStmt::const_body_iterator I = stmt->body_begin (), E =
	stmt->body_end (); I != E; ++I)
      {
	if (I != stmt->body_begin ())
	  {
	    line () << "; ";
	  }
	go (*I);
      }
    nobreak () << "|s])";
    outdent ();
  }

  void
  VisitNullStmt(const NullStmt *stmt)
  {
    line() << "Sskip";
  }

private:
  ASTContext *Context;

};

Outputter* defaultOutput = &Outputter::outs;

void
declToCoq (ASTContext *ctxt, const clang::Decl* decl)
{
  ToCoq (ctxt).goDecl (decl);
}

void
stmtToCoq (ASTContext *ctxt, const clang::Stmt* stmt)
{
  ToCoq (ctxt).goStmt (stmt);
}

