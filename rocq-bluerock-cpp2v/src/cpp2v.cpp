/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is based on the tutorial here:
 * https://clang.llvm.org/docs/LibASTMatchersTutorial.html
 * See the LICENSE-LLVM file in the repositroy root for details.
 *
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
#include "Trace.hpp"
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
static cl::extrahelp CommonHelp(
	"\nACTUAL USAGE: cpp2v [cpp2v options] <source> -- [clang options]\n");

static cl::opt<std::string> NamesFile("names",
									  cl::desc("print notation for C++ names"),
									  cl::value_desc("filename"), cl::Optional,
									  cl::cat(Cpp2V));

static cl::opt<std::string> VFileOutput("module",
										cl::desc("print translation unit"),
										cl::value_desc("filename"),
										cl::Optional, cl::cat(Cpp2V));
static cl::alias DashO("o", cl::desc("alias for --module"),
					   cl::value_desc("filename"), cl::aliasopt(VFileOutput));

static cl::opt<bool> Verbose("v", cl::desc("verbose"), cl::Optional,
							 cl::cat(Cpp2V));
static cl::opt<bool> Verboser("vv", cl::desc("verboser"), cl::Optional,
							  cl::cat(Cpp2V));
static cl::opt<bool> Quiet("q", cl::desc("quiet"), cl::Optional,
						   cl::cat(Cpp2V));

static cl::opt<bool> Comment("comment", cl::desc("include name comments"),
							 cl::Optional, cl::cat(Cpp2V));

static cl::opt<bool> NoElaborate(
	"no-elaborate",
	cl::desc("do not elaborate templates and un-forced definitions"),
	cl::Optional, cl::cat(Cpp2V));

static cl::opt<bool> Version("cpp2v-version",
							 cl::desc("print version and exit"), cl::Optional,
							 cl::ValueOptional, cl::cat(Cpp2V));

static cl::opt<std::string> Templates("templates", cl::desc("print templates"),
									  cl::value_desc("filename"), cl::Optional,
									  cl::cat(Cpp2V));

static cl::opt<bool>
	MangledKeys("mangled-keys",
				cl::desc("use mangled names as keys in translation units"),
				cl::Optional, cl::cat(Cpp2V));

static cl::opt<std::string> NameTest("name-test",
									 cl::desc("print structured names"),
									 cl::value_desc("filename"), cl::Optional,
									 cl::cat(Cpp2V));

static cl::opt<bool> CheckTypes("check-types",
								cl::desc("check types of translation units"),
								cl::Optional, cl::ValueOptional,
								cl::cat(Cpp2V));

static cl::bits<Trace::Bit> TraceBits(
	"trace", cl::desc("print debug trace on fd 2 (can be repeated)"),
	cl::ZeroOrMore, cl::CommaSeparated,
	cl::values(clEnumValN(Trace::Bit::Elaborate, "Elaborate",
						  "trace definition of implicits"),
			   clEnumValN(Trace::Bit::ModuleBuilder, "ModuleBuilder",
						  "trace declaration filter"),
			   clEnumValN(Trace::Bit::Decl, "Decl",
						  "trace declaration printer"),
			   clEnumValN(Trace::Bit::Name, "Name", "trace name printer"),
			   clEnumValN(Trace::Bit::Type, "Type", "trace type printer"),
			   clEnumValN(Trace::Bit::Local, "Local",
						  "trace local declaration printer"),
			   clEnumValN(Trace::Bit::Stmt, "Stmt", "trace statement printer"),
			   clEnumValN(Trace::Bit::Expr, "Expr", "trace expression printer"),
			   clEnumValN(Trace::Bit::ALL, "ALL", "trace everything")),
	cl::cat(Cpp2V));

static cl::opt<bool> NoSharing("no-sharing", cl::desc("disable sharing"),
							   cl::Optional, cl::ValueOptional, cl::cat(Cpp2V));

static cl::opt<bool>
	NoAliases("no-aliases",
			  cl::desc("do not emit typedef and using declarations"),
			  cl::Optional, cl::ValueOptional, cl::cat(Cpp2V));

class ToCoqAction : public clang::ASTFrontendAction {
public:
	virtual std::unique_ptr<clang::ASTConsumer>
	CreateASTConsumer(clang::CompilerInstance &Compiler,
					  llvm::StringRef InFile) override {
#if 0
	Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames.push_back(
		"with");
	Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames.push_back(
		"internal");
	for (auto i :
		 Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames) {
		llvm::errs() << i << "\n";
	}
#endif
		auto result =
			new ToCoqConsumer(&Compiler, to_opt(VFileOutput), to_opt(NamesFile),
							  to_opt(Templates), to_opt(NameTest), !MangledKeys,
							  Trace::fromBits(TraceBits.getBits()), Comment,
							  !NoSharing, CheckTypes, !NoElaborate, !NoAliases);
		return std::unique_ptr<clang::ASTConsumer>(result);
	}

	template<typename T>
	std::optional<T> to_opt(const cl::opt<T> &val) {
		if (val.empty()) {
			return std::optional<T>();
		} else {
			return std::optional<T>(val.getValue());
		}
	}

	virtual bool BeginSourceFileAction(CompilerInstance &CI) override {
		return this->clang::ASTFrontendAction::BeginSourceFileAction(CI);
	}
};

int
main(int argc, const char **argv) {
	auto MaybeOptionsParser = CommonOptionsParser::create(argc, argv, Cpp2V);
	if (not MaybeOptionsParser) {
		llvm::errs() << MaybeOptionsParser.takeError();
		return 1;
	}

	auto &OptionsParser = MaybeOptionsParser.get();

	if (Version) {
		llvm::errs() << "cpp2v version " << cpp2v::VERSION << "\n";
		return 0;
	}

	logging::set_level(logging::UNSUPPORTED);
	if (Verboser) {
		logging::set_level(logging::VERBOSER);
	} else if (Verbose) {
		logging::set_level(logging::VERBOSE);
	} else if (Quiet) {
		logging::set_level(logging::NONE);
	}

	ClangTool Tool(OptionsParser.getCompilations(),
				   OptionsParser.getSourcePathList());

	return Tool.run(newFrontendActionFactory<ToCoqAction>().get());
}
