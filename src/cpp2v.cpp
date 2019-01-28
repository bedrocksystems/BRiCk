#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"

#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CommonOptionsParser.h"
// Declares clang::SyntaxOnlyAction.
#include "clang/Frontend/FrontendActions.h"
// Declares llvm::cl::extrahelp.
#include "llvm/Support/CommandLine.h"

#include "ToCoq.hpp"

using namespace clang;


class ToCoqConsumer : public clang::ASTConsumer {
public:
  explicit ToCoqConsumer(ASTContext *Context)
    : ctxt(Context) {}

  virtual void HandleTranslationUnit(clang::ASTContext &Context) {
    toCoqModule(this->ctxt, Context.getTranslationUnitDecl());
  }
private:
  ASTContext* ctxt;
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
static cl::OptionCategory Cpp2V("cpp2v options");

// CommonOptionsParser declares HelpMessage with a description of the common
// command-line options related to the compilation database and input files.
// It's nice to have this help message in all tools.
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

// todo(gmm): i need to figure out how to thread this value through so that we
// output to that file.
// static cl::opt<StringRef> VFileOutput("out", cl::cat(Cpp2V));

int main(int argc, const char **argv) {
  CommonOptionsParser OptionsParser(argc, argv, Cpp2V);
  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());
  return Tool.run(newFrontendActionFactory<ToCoqAction>().get());
}
