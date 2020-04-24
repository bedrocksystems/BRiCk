/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
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

using namespace clang;
using namespace clang::tooling;
using namespace llvm;
#include "Version.hpp"
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Sema/Sema.h"
#include "llvm/Support/raw_ostream.h"
using namespace clang;

namespace {

class ToCoqAction : public PluginASTAction {

protected:
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                   llvm::StringRef) override {
        return std::make_unique<ToCoqConsumer>(VFileOutput, SpecFile,
                                                NamesFile);
    }

    bool ParseArgs(const CompilerInstance &CI,
                   const std::vector<std::string> &args) override {
        DiagnosticsEngine &D = CI.getDiagnostics();
        for (unsigned i = 0, e = args.size(); i != e; ++i) {
            if (args[i] == "-o") {
                if (++i == e) {
                    unsigned DiagID = D.getCustomDiagID(
                        DiagnosticsEngine::Error, "-o is missing parameter");
                    D.Report(DiagID) << args[i];
                    return false;
                }
                VFileOutput = args[i];
            } else if (args[i] == "-names") {
                if (++i == e) {
                    unsigned DiagID = D.getCustomDiagID(
                        DiagnosticsEngine::Error, "-names is missing parameter");
                    D.Report(DiagID) << args[i];
                    return false;
                }
                NamesFile = args[i];
            }
        }
        if (!args.empty() && args[0] == "help")
            PrintHelp(llvm::errs());

        return true;
    }
    void PrintHelp(llvm::raw_ostream &ros) {
        ros << "cpp2v_plugin version " << cpp2v::VERSION << "\n";
    }

private:
    Optional<std::string> VFileOutput;
    Optional<std::string> SpecFile;
    Optional<std::string> NamesFile;
};

}

static FrontendPluginRegistry::Add<ToCoqAction> X("cpp2v",
                                                  "generate a Coq AST");
