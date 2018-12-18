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

class ToCoq : public ConstStmtVisitor<ToCoq, void>, public ConstDeclVisitor<
    ToCoq, void>, public TypeVisitor<ToCoq, void>
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
    line () << "Dtype \"" << type->getNameAsString () << "\"...";
  }

  void
  VisitCXXRecordDecl (const CXXRecordDecl *Declaration)
  {
    line () << "class declaration " << Declaration->getNameAsString () << "\n";
  }

  void
  VisitFunctionDecl (const FunctionDecl *decl)
  {
    line () << "Dfunction \"" << decl->getNameAsString () << "\" [";
    for (auto i = decl->param_begin (), e = decl->param_end (); i != e;)
      {

	line () << "(\"" << (*i)->getNameAsString () << "\", ";
	goType ((*i)->getType ().getTypePtr ());
	line () << ")";
	if (++i != e)
	  {
	    line () << ";";
	  }
      }
    indent ();
    go (decl->getBody ());
    outdent ();
  }

  void
  VisitVarDecl (const VarDecl *decl)
  {
    line () << "Dvar \"" << decl->getNameAsString () << "\" ";
    indent ();
    goType (decl->getType ().getTypePtr ());
    if (decl->hasInit ())
      {
	line () << "(Some (";
	go (decl->getInit ());
	line () << "))";
      }
    else
      {
	line () << "None";
      }
    outdent ();
  }

  // Visiting statements
  void
  VisitDeclStmt (const DeclStmt* decl)
  {
    line () << "Sdeclaration [";
    if (decl->isSingleDecl ())
      {
	indent ();
	go (decl->getSingleDecl ());
	outdent ();
	line () << "]";
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
  }

  void
  VisitBinaryOperator (const BinaryOperator *expr)
  {
    line () << "Ebinop \"" << expr->getOpcodeStr () << "\"";
    indent ();
    go (expr->getLHS ());
    go (expr->getRHS ());
    outdent ();
  }

  void
  VisitDeclRefExpr (const DeclRefExpr *expr)
  {
    line () << "Eref \"" << expr->getDecl ()->getNameAsString () << "\"";
  }

  void
  VisitCallExpr (const CallExpr *expr)
  {
    line () << "Ecall";
    indent ();
    go (expr->getCallee ());
    line () << "[";
    indent ();
    for (CallExpr::const_arg_iterator i = expr->arg_begin (), e =
	expr->arg_end (); i != e; ++i)
      {
	go (*i);
      }
    outdent ();
    line () << "]";
    outdent ();
  }

  void
  VisitCastExpr (const CastExpr *expr)
  {
    line () << "Ecast \"" << expr->getCastKindName () << "\" ";
    indent ();
    go (expr->getSubExpr ());
    outdent ();
  }

  void
  VisitIntegerLiteral (const IntegerLiteral *lit)
  {
    line () << "Eint " << lit->getValue () << " ";
    goType (lit->getType ().getTypePtr ());
  }

  void
  VisitReturnStmt (const ReturnStmt *stmt)
  {
    line () << "Sreturn";
    indent ();
    go (stmt->getRetValue ());
    outdent ();
  }

  void
  VisitCompoundStmt (const CompoundStmt *stmt)
  {
    line () << "Sseq [";
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
    line () << "]";
    outdent ();
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

