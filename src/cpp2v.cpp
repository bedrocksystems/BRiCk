/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License. 
 * See the LICENSE-BedRock file in the repository root for details. 
 *
 * This file is based on the tutorial here:
 * https://clang.llvm.org/docs/LibASTMatchersTutorial.html
 */
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include <optional>

#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
// Declares clang::SyntaxOnlyAction.
#include "clang/Frontend/FrontendActions.h"
// Declares llvm::cl::extrahelp.
#include "llvm/Support/CommandLine.h"

#include "Logging.hpp"
#include "ToCoq.hpp"
#include "Version.hpp"

using namespace clang;
using namespace clang::tooling;
using namespace llvm;

// Apply a custom category to all command-line options so that they are the
// only ones displayed.
static cl::OptionCategory Cpp2V("cpp2v options");

// CommonOptionsParser declares HelpMessage with a description of the common
// command-line options related to the compilation database and input files.
// It's nice to have this help message in all tools.
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

static cl::opt<std::string>
    SpecFile("spec", cl::desc("path to generate specifications"), cl::Optional,
             cl::cat(Cpp2V));

static cl::opt<std::string> NamesFile("names",
                                      cl::desc("path to generate names"),
                                      cl::Optional, cl::cat(Cpp2V));

static cl::opt<std::string> VFileOutput("o",
                                        cl::desc("path to generate the module"),
                                        cl::Optional, cl::cat(Cpp2V));

static cl::opt<bool> Verbose("v", cl::desc("verbose"), cl::Optional,
                             cl::cat(Cpp2V));
static cl::opt<bool> Verboser("vv", cl::desc("verboser"), cl::Optional,
                              cl::cat(Cpp2V));

static cl::opt<bool> Version("cpp2v-version", cl::Optional, cl::ValueOptional,
                             cl::cat(Cpp2V));

class ToCoqAction : public clang::ASTFrontendAction {
public:
    virtual std::unique_ptr<clang::ASTConsumer>
    CreateASTConsumer(clang::CompilerInstance &Compiler,
                      llvm::StringRef InFile) override {
#if 0
		Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames.push_back("with");
		Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames.push_back("internal");
    for (auto i : Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames) {
			llvm::errs() << i << "\n";
		}
#endif
        auto result = new ToCoqConsumer(&Compiler, to_opt(VFileOutput),
                                        to_opt(SpecFile), to_opt(NamesFile));
        return std::unique_ptr<clang::ASTConsumer>(result);
    }

    template<typename T>
    Optional<T> to_opt(const cl::opt<T> &val) {
        if (val.empty()) {
            return Optional<T>();
        } else {
            return Optional<T>(val.getValue());
        }
    }

    virtual bool BeginSourceFileAction(CompilerInstance &CI) override {
        // Because we enable incremental processing, we must call [ActOnEndOfTranslationUnit]
        // explicitly.
        CI.getPreprocessor().enableIncrementalProcessing();
        return this->clang::ASTFrontendAction::BeginSourceFileAction(CI);
    }
};

int
main(int argc, const char **argv) {
    CommonOptionsParser OptionsParser(argc, argv, Cpp2V);

    if (Version) {
        llvm::errs() << "cpp2v version " << cpp2v::VERSION << "\n";
        return 0;
    }

    if (Verboser) {
        logging::set_level(logging::VERBOSER);
    } else if (Verbose) {
        logging::set_level(logging::VERBOSE);
    } else {
        logging::set_level(logging::NONE);
    }

    ClangTool Tool(OptionsParser.getCompilations(),
                   OptionsParser.getSourcePathList());

    return Tool.run(newFrontendActionFactory<ToCoqAction>().get());
}
