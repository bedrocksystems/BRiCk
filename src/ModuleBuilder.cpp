/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ModuleBuilder.hpp"
#include "CommentScanner.hpp"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "SpecCollector.hpp"
#include "FromClang.hpp"
#include "clang/Basic/Builtins.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include <set>

using namespace clang;

static void
unsupported_decl(const Decl* decl) {
    using namespace logging;
    debug() << "[DEBUG] unsupported declaration kind \""
        << decl->getDeclKindName() << "\", dropping.\n";
}

using Flags = ::Module::Flags;

class Elaborate : public DeclVisitorArgs<Elaborate, void, Flags> {
private:
    using Visitor = DeclVisitorArgs<Elaborate, void, Flags>;

    clang::CompilerInstance *const ci_;
    std::set<int64_t> visited_;
    const bool templates_;

public:
    Elaborate(clang::CompilerInstance *ci, bool templates) : ci_(ci), templates_(templates) {}

    void Visit(Decl *d, Flags flags) {
        if (visited_.find(d->getID()) == visited_.end()) {
            visited_.insert(d->getID());
            Visitor::Visit(d, flags);
        }
    }

    void VisitDecl(const Decl *d, Flags) {
        unsupported_decl(d);
    }

    void VisitVarTemplateDecl(const VarTemplateDecl *decl, Flags flags) {
        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitTranslationUnitDecl(const TranslationUnitDecl *decl, Flags flags) {
        assert(flags.none());

        for (auto i : decl->decls()) {
            this->Visit(i, flags);
        }
    }

    void GenerateImplicitMembers(CXXRecordDecl *decl, bool deprecated) {
        Sema &sema = ci_->getSema();
        if (deprecated) {
            sema.ForceDeclarationOfImplicitMembers(decl);
            return;
        }
        GenerateUndeprecatedImplicitMembers(decl, sema);
    }

    void VisitCXXRecordDecl(CXXRecordDecl *decl, Flags flags) {
        if (decl->isImplicit()) {
            return;
        }
        if (!flags.in_specialization && isa<ClassTemplateSpecializationDecl>(decl)) {
            return;
        }

        if (decl->isCompleteDefinition()) {
            // Do *not* generate deprecated members
            GenerateImplicitMembers(decl, false);
        }

        // find any static functions or fields
        for (auto i : decl->decls()) {
            Visit(i, flags);
        }
    }

    void VisitCXXMethodDecl(CXXMethodDecl *decl, Flags) {
        if (decl->isDeleted() || (!templates_ && decl->isDependentContext()))
            return;

        if (not decl->getBody() && decl->isDefaulted()) {
            if (decl->isMoveAssignmentOperator()) {
                ci_->getSema().DefineImplicitMoveAssignment(decl->getLocation(),
                                                            decl);

            } else if (decl->isCopyAssignmentOperator()) {
                ci_->getSema().DefineImplicitCopyAssignment(decl->getLocation(),
                                                            decl);
            } else {
                logging::log() << "Didn't generate body for defaulted method\n";
            }
        }
    }

    void VisitNamespaceDecl(const NamespaceDecl *decl, Flags flags) {
        assert(flags.none());

        for (auto d : decl->decls()) {
            this->Visit(d, flags);
        }
    }

    void VisitLinkageSpecDecl(const LinkageSpecDecl *decl, Flags flags) {
        assert(flags.none());

        for (auto i : decl->decls()) {
            this->Visit(i, flags);
        }
    }

    void VisitCXXConstructorDecl(CXXConstructorDecl *decl, Flags flags) {
        if (decl->isDeleted())
            return;

        if (not decl->getBody() && decl->isDefaulted()) {
            if (decl->isDefaultConstructor()) {
                ci_->getSema().DefineImplicitDefaultConstructor(
                    decl->getLocation(), decl);
            } else if (decl->isCopyConstructor()) {
                ci_->getSema().DefineImplicitCopyConstructor(
                    decl->getLocation(), decl);
            } else if (decl->isMoveConstructor()) {
                ci_->getSema().DefineImplicitMoveConstructor(
                    decl->getLocation(), decl);
            } else {
                logging::debug() << "Unknown defaulted constructor.\n";
            }
        }

        this->DeclVisitorArgs::VisitCXXConstructorDecl(decl, flags);
    }

    void VisitCXXDestructorDecl(CXXDestructorDecl *decl, Flags) {
        if (decl->isDeleted())
            return;

        if (not decl->hasBody() && decl->isDefaulted()) {
            ci_->getSema().DefineImplicitDestructor(decl->getLocation(), decl);
        }
    }

    void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl, Flags flags) {
        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitClassTemplateDecl(const ClassTemplateDecl *decl, Flags flags) {
        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitFriendDecl(const FriendDecl *decl, Flags flags) {
        if (decl->getFriendDecl()) {
            this->Visit(decl->getFriendDecl(), flags);
        }
    }
};

class BuildModule : public ConstDeclVisitorArgs<BuildModule, void, Flags> {
private:
    using Visitor = ConstDeclVisitorArgs<BuildModule, void, Flags>;

    ::Module &module_;
    Filter &filter_;
    const bool templates_;
    SpecCollector &specs_;
    clang::ASTContext *const context_;
    std::set<int64_t> visited_;

private:
    Filter::What go(const NamedDecl *decl, Flags flags, bool definition = true) {
        auto what = filter_.shouldInclude(decl);
        switch (what) {
        case Filter::What::DEFINITION:
            if (definition) {
                module_.add_definition(decl, flags);
                return what;
            } else {
                module_.add_declaration(decl, flags);
                return Filter::What::DECLARATION;
            }
        case Filter::What::DECLARATION:
            module_.add_declaration(decl, flags);
            return Filter::What::DECLARATION;
        default:
            return Filter::What::NOTHING;
        }
    }

public:
    BuildModule(::Module &m, Filter &filter, bool templates, clang::ASTContext *context,
                SpecCollector &specs, clang::CompilerInstance *ci)
        : module_(m), filter_(filter), templates_(templates), specs_(specs), context_(context) {}

    void Visit(const Decl *d, Flags flags) {
        if (visited_.find(d->getID()) == visited_.end()) {
            visited_.insert(d->getID());
            Visitor::Visit(d, flags);
        }
    }

    void VisitDecl(const Decl *d, Flags) {
        unsupported_decl(d);
    }

    void VisitBuiltinTemplateDecl(const BuiltinTemplateDecl *, Flags) {
        // ignore
    }

    void VisitVarTemplateDecl(const VarTemplateDecl *decl, Flags flags) {
        if (templates_)
            go(decl, flags.set_template());

        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitStaticAssertDecl(const StaticAssertDecl *decl, Flags) {
        module_.add_assert(decl);
    }

    void VisitAccessSpecDecl(const AccessSpecDecl *, Flags) {
        // ignore
    }

    void VisitTranslationUnitDecl(const TranslationUnitDecl *decl, Flags flags) {
        assert(flags.none());

        for (auto i : decl->decls()) {
            this->Visit(i, flags);
        }
    }

    void VisitTypeDecl(const TypeDecl *type, Flags) {
        /*
        TODO: Consolidate code for complaining about and dumping
        unsupported things.
        */
        logging::log() << "Error: Unsupported type declaration: "
                       << type->getQualifiedNameAsString()
                       << "(type = " << type->getDeclKindName() << ")\n";
    }

    void VisitEmptyDecl(const EmptyDecl *decl, Flags) {}

    void VisitTypedefNameDecl(const TypedefNameDecl *type, Flags flags) {
        go(type, flags);
    }

    void VisitTagDecl(const TagDecl *decl, Flags flags) {
        auto defn = decl->getDefinition();
        if (defn == decl) {
            go(decl, flags, true);
        } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
            go(decl, flags, false);
        }
    }

    void VisitCXXRecordDecl(const CXXRecordDecl *decl, Flags flags) {
        if (decl->isImplicit()) {
            return;
        }
        if (!flags.in_specialization && isa<ClassTemplateSpecializationDecl>(decl)) {
            return;
        }

        // find any static functions or fields
        for (auto i : decl->decls()) {
            Visit(i, flags);
        }

        VisitTagDecl(decl, flags);
    }

    void VisitCXXMethodDecl(const CXXMethodDecl *decl, Flags flags) {
        if (decl->isDeleted())
            return;

        this->ConstDeclVisitorArgs::VisitCXXMethodDecl(decl, flags);
    }

    void VisitFunctionDecl(const FunctionDecl *decl, Flags flags) {
        if (!templates_ && decl->isDependentContext()) {
            return;
        }

        using namespace comment;
        auto defn = decl->getDefinition();
        if (defn == decl) {
            if (auto c = context_->getRawCommentForDeclNoCache(decl)) {
                this->specs_.add_specification(decl, c, *context_);
            }

            if (go(decl, flags, true) >= Filter::What::DEFINITION) {
                // search for static local variables
                for (auto i : decl->decls()) {
                    if (auto d = dyn_cast<VarDecl>(i)) {
                        if (d->isStaticLocal()) {
                            go(d, flags);
                        }
                    }
                }
            }
        } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
            go(decl, flags, false);
        }
    }

    void VisitEnumConstantDecl(const EnumConstantDecl *decl, Flags flags) {
        go(decl, flags);
    }

    void VisitVarDecl(const VarDecl *decl, Flags flags) {
        if (!templates_ && !decl->isTemplated()) {
            return;
        }

        go(decl, flags);
    }

    void VisitFieldDecl(const FieldDecl *, Flags) {
        // ignore
    }

    void VisitUsingDecl(const UsingDecl *, Flags) {
        // ignore
    }

    void VisitUsingDirectiveDecl(const UsingDirectiveDecl *, Flags) {
        // ignore
    }

    void VisitIndirectFieldDecl(const IndirectFieldDecl *, Flags) {
        // ignore
    }

    void VisitNamespaceDecl(const NamespaceDecl *decl, Flags flags) {
        assert(flags.none());

        for (auto d : decl->decls()) {
            this->Visit(d, flags);
        }
    }

    void VisitEnumDecl(const EnumDecl *decl, Flags flags) {
        if (not decl->isCanonicalDecl())
            return;

        go(decl, flags);
        for (auto i : decl->enumerators()) {
            go(i, flags);
        }
    }

    void VisitLinkageSpecDecl(const LinkageSpecDecl *decl, Flags flags) {
        assert(flags.none());

        for (auto i : decl->decls()) {
            this->Visit(i, flags);
        }
    }

    void VisitCXXConstructorDecl(const CXXConstructorDecl *decl, Flags flags) {
        if (decl->isDeleted())
            return;

        this->ConstDeclVisitorArgs::VisitCXXConstructorDecl(decl, flags);
    }

    void VisitCXXDestructorDecl(const CXXDestructorDecl *decl, Flags flags) {
        if (decl->isDeleted())
            return;

        this->ConstDeclVisitorArgs::VisitCXXDestructorDecl(decl, flags);
    }

    void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl, Flags flags) {
        if (templates_)
            go(decl, flags.set_template());

        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitClassTemplateDecl(const ClassTemplateDecl *decl, Flags flags) {
        if (templates_)
            this->Visit(decl->getTemplatedDecl(), flags.set_template());

        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitFriendDecl(const FriendDecl *decl, Flags flags) {
        if (decl->getFriendDecl()) {
            this->Visit(decl->getFriendDecl(), flags);
        }
    }

    void VisitTypeAliasTemplateDecl(const TypeAliasTemplateDecl *, Flags) {
        // ignore
    }

    void VisitUsingShadowDecl(const UsingShadowDecl *, Flags) {
        // ignore
    }
};

void
build_module(clang::TranslationUnitDecl *tu, ::Module &mod, Filter &filter,
             SpecCollector &specs, clang::CompilerInstance *ci,
             bool elaborate, bool templates) {

    Flags flags {};

    if (elaborate) {
        // First we do all of the elaboration that we want that is not strictly
        // necessary from the standard, e.g. generating defaultable operations
        // such as constructors, destructors, assignment operators.
        // Generating them eagerly makes it possible to verify them in the
        // header file rather than waiting until they are first used.
        //
        // CAVEAT: this approach only gets 1-step of elaboration, if completing
        // the translation unit below (by calling [ActOnEndOfTranslationUnit])
        // introduces new classes, then we don't have an opportunity to elaborate
        // those classes.
        //
        // An alternative (better?) solution is to express the semantics of
        // defaulted operations within the semantics and *prevent* generating
        // these at all. This would decrease our file representation size and
        // bring us a little bit closer to the semantics rather than relying
        // on choices for how clang implements defaulted operations.
        Elaborate(ci, templates).VisitTranslationUnitDecl(tu, flags);

        // Once we are done visiting the AST, we run all the actions that
        // are pending in the translation unit.
        // We need to do this because when we parse with elaboration enabled,
        // we parse in "incremental" mode. Ending the translation unit generates
        // all of the template specializations, etc.
        ci->getSema().ActOnEndOfTranslationUnit();
    }

    auto &ctxt = tu->getASTContext();
    BuildModule(mod, filter, templates, &ctxt, specs, ci)
        .VisitTranslationUnitDecl(tu, flags);
}

void ::Module::add_assert(const clang::StaticAssertDecl* d) {
    asserts_.push_back(d);
}

using DeclList = ::Module::DeclList;

static void
add_decl(DeclList& decls, DeclList& tdecls, const clang::NamedDecl *d, Flags flags) {
    if (flags.in_template) {
        tdecls.push_back(d);
    } else {
        decls.push_back(d);
        if (flags.in_specialization) {
            tdecls.push_back(d);
        }
    }
}

void ::Module::add_definition(const clang::NamedDecl *d, Flags flags) {
    add_decl(definitions_, template_definitions_, d, flags);
}

void ::Module::add_declaration(const clang::NamedDecl *d, Flags flags) {
    add_decl(declarations_, template_declarations_, d, flags);
}
