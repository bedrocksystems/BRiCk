#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"

#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CommonOptionsParser.h"
// Declares clang::SyntaxOnlyAction.
#include "clang/Frontend/FrontendActions.h"
// Declares llvm::cl::extrahelp.
#include "llvm/Support/CommandLine.h"


using namespace clang;

class ToCoq
  : public RecursiveASTVisitor<ToCoq> {
private:
    llvm::raw_ostream& line() const;

    void indent();
    void outdent();

    void go(Decl *d) {
        RecursiveASTVisitor<ToCoq>::TraverseDecl(d);
    }
    void go(Stmt *s) {
        RecursiveASTVisitor<ToCoq>::TraverseStmt(s);
    }

public:
  explicit ToCoq(ASTContext *Context)
    : Context(Context), depth(0) {}

    // bool VisitConditionalStmt(IfStmt
  bool TraverseFunctionDecl(FunctionDecl *decl) {
      line() << "Dfunction "
             << decl->getNameAsString();
      indent();
      go(decl->getBody());
      outdent();
      return true;
  }

  bool TraverseDeclStmt(DeclStmt* decl) {
      line() << "Sdeclaration";
      if (decl->isSingleDecl()) {
          indent();
          go(decl->getSingleDecl());
          outdent();
      } else {
          indent();
          for (DeclGroupRef::iterator i = decl->decl_begin() , e = decl->decl_end(); i != e; ++i) {
              go(*i);
          }
          outdent();
      }
      return true;
  }

  bool TraverseVarDecl(VarDecl *decl) {
      line() << "Dvar \"" << decl->getNameAsString() << "\" ";
      if (decl->hasInit()) {
          line() << "(Some";
          go(decl->getInit());
          line() << ")";
      } else {
          line() << "None";
      }
      return true;
  }

  bool TraverseBinOp(BinaryOperator *expr) {
      line() << "Ebinop \"" << expr->getOpcodeStr() << "\"";
      indent();
      go(expr->getLHS());
      go(expr->getRHS());
      outdent();
      return true;
  }

  bool TraverseDeclRefExpr(DeclRefExpr *expr) {
      line() << "Eref \"" << expr->getDecl()->getNameAsString() << "\"";
      return true;
  }

  bool TraverseCallExpr(CallExpr *expr) {
      line() << "Ecall";
      indent();
      go(expr->getCallee());
      line() << "[";
      indent();
      for (CallExpr::arg_iterator i = expr->arg_begin() , e = expr->arg_end(); i != e; ++i) {
          go(*i);
      }
      outdent();
      line() << "]";
      outdent();
      return true;
  }

  bool TraverseCastExpr(CastExpr *expr) {
      line() << "Ecast \"" << expr->getCastKindName() << " ";
      indent();
      go(expr->getSubExpr());
      outdent();
      return true;
  }

  bool TraverseCXXRecordDecl(CXXRecordDecl *Declaration) {
      line() << "class declaration "
             << Declaration->getNameAsString()
             << "\n";
      return true;
  }

  bool TraverseIntegerLiteral(IntegerLiteral *lit) {
      line() << "Eint " << lit->getValue();
      return true;
  }

  bool TraverseReturnStmt(ReturnStmt *stmt) {
      line() << "Sreturn";
      indent();
      go(stmt->getRetValue());
      outdent();
      return true;
  }

  bool TraverseCompoundStmt(CompoundStmt *stmt) {
      line() << "Sseq";
      indent();
        for (clang::CompoundStmt::body_iterator I = stmt->body_begin(),
                 E = stmt->body_end(); I != E; ++I) {
            go(*I);
        }
      outdent();
      return true;
  }

  // bool VisitCXXRecordDecl(CXXRecordDecl *Declaration) {
  //   if (Declaration->getQualifiedNameAsString() == "n::m::C") {
  //     FullSourceLoc FullLocation = Context->getFullLoc(Declaration->getBeginLoc());
  //     if (FullLocation.isValid())
  //       llvm::outs() << "Found declaration at "
  //                    << FullLocation.getSpellingLineNumber() << ":"
  //                    << FullLocation.getSpellingColumnNumber() << "\n";
  //   }
  //   return true;
  // }

private:
  ASTContext *Context;

  unsigned int depth;
};

llvm::raw_ostream& ToCoq::line() const {
    llvm::outs() << "\n";
    unsigned int d = this->depth;
    while (d--) {
        llvm::outs() << " ";
    }
    return llvm::outs();
}

void ToCoq::indent() { this->depth += 2; }
void ToCoq::outdent() {
    assert(this->depth >= 2);
    this->depth -= 2;
}


class ToCoqConsumer : public clang::ASTConsumer {
public:
  explicit ToCoqConsumer(ASTContext *Context)
    : Visitor(Context) {}

  virtual void HandleTranslationUnit(clang::ASTContext &Context) {
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
  }
private:
  ToCoq Visitor;
};

class ToCoqAction : public clang::ASTFrontendAction {
public:
  virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
    clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    return std::unique_ptr<clang::ASTConsumer>(
        new ToCoqConsumer(&Compiler.getASTContext()));
  }
};

using namespace clang::tooling;
using namespace llvm;

// Apply a custom category to all command-line options so that they are the
// only ones displayed.
static cl::OptionCategory MyToolCategory("cpp2v options");

// CommonOptionsParser declares HelpMessage with a description of the common
// command-line options related to the compilation database and input files.
// It's nice to have this help message in all tools.
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

int main(int argc, const char **argv) {
  CommonOptionsParser OptionsParser(argc, argv, MyToolCategory);
  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());
  return Tool.run(newFrontendActionFactory<ToCoqAction>().get());
}
