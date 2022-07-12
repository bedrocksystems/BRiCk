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
#include "clang/Basic/Builtins.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include <set>

using namespace clang;

class Elaborate : public DeclVisitorArgs<Elaborate, void, bool> {
private:
    clang::CompilerInstance *const ci_;
    std::set<int64_t> visited_;

public:
    Elaborate(clang::CompilerInstance *ci) : ci_(ci) {}

    void Visit(Decl *d, bool s) {
        if (visited_.find(d->getID()) == visited_.end()) {
            visited_.insert(d->getID());
            DeclVisitorArgs<Elaborate, void, bool>::Visit(d, s);
        }
    }

    void VisitDecl(const Decl *d, bool) {
        logging::debug() << "Unknown declaration kind \""
                         << d->getDeclKindName() << "\", dropping.\n";
    }

    void VisitVarTemplateDecl(const VarTemplateDecl *decl, bool) {
        for (auto i : decl->specializations()) {
            this->Visit(i, true);
        }
    }

    void VisitTranslationUnitDecl(const TranslationUnitDecl *decl, bool) {
        for (auto i : decl->decls()) {
            this->Visit(i, false);
        }
    }

    void VisitCXXRecordDecl(CXXRecordDecl *decl, bool is_specialization) {
        if (decl->isImplicit()) {
            return;
        }
        if (!is_specialization && isa<ClassTemplateSpecializationDecl>(decl)) {
            return;
        }

        if (not(decl->isImplicit() /* or decl->isAnonymousStructOrUnion() */)) {
            ci_->getSema().ForceDeclarationOfImplicitMembers(decl);
        }

        // find any static functions or fields
        for (auto i : decl->decls()) {
            Visit(i, false);
        }
    }
    void VisitCXXMethodDecl(CXXMethodDecl *decl, bool) {
        if (decl->isDeleted() or decl->isDependentContext())
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

    void VisitNamespaceDecl(const NamespaceDecl *decl, bool) {
        for (auto d : decl->decls()) {
            this->Visit(d, false);
        }
    }

    void VisitLinkageSpecDecl(const LinkageSpecDecl *decl, bool) {
        for (auto i : decl->decls()) {
            this->Visit(i, false);
        }
    }

    void VisitCXXConstructorDecl(CXXConstructorDecl *decl, bool) {
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

        this->DeclVisitorArgs::VisitCXXConstructorDecl(decl, false);
    }

    void VisitCXXDestructorDecl(CXXDestructorDecl *decl, bool) {
        if (decl->isDeleted())
            return;

        if (not decl->hasBody() && decl->isDefaulted()) {
            ci_->getSema().DefineImplicitDestructor(decl->getLocation(), decl);
        }
    }

    void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl, bool) {
        // note(gmm): for now, i am just going to return the specializations.
        for (auto i : decl->specializations()) {
            this->Visit(i, true);
        }
    }

    void VisitClassTemplateDecl(const ClassTemplateDecl *decl, bool) {
        for (auto i : decl->specializations()) {
            this->Visit(i, true);
        }
    }

    void VisitFriendDecl(const FriendDecl *decl, bool) {
        if (decl->getFriendDecl()) {
            this->Visit(decl->getFriendDecl(), true);
        }
    }
};

class BuildModule : public ConstDeclVisitorArgs<BuildModule, void, bool> {
private:
    ::Module &module_;
    Filter &filter_;
    SpecCollector &specs_;
    clang::ASTContext *const context_;
    std::set<int64_t> visited_;

private:
    Filter::What go(const NamedDecl *decl, bool definition = true) {
        auto what = filter_.shouldInclude(decl);
        switch (what) {
        case Filter::What::DEFINITION:
            if (definition) {
                module_.add_definition(decl);
                return what;
            } else {
                module_.add_declaration(decl);
                return Filter::What::DECLARATION;
            }
        case Filter::What::DECLARATION:
            module_.add_declaration(decl);
            return Filter::What::DECLARATION;
        default:
            return Filter::What::NOTHING;
        }
    }

public:
    BuildModule(::Module &m, Filter &filter, clang::ASTContext *context,
                SpecCollector &specs, clang::CompilerInstance *ci)
        : module_(m), filter_(filter), specs_(specs), context_(context) {}

    void Visit(const Decl *d, bool s) {
        if (visited_.find(d->getID()) == visited_.end()) {
            visited_.insert(d->getID());
            ConstDeclVisitorArgs<BuildModule, void, bool>::Visit(d, s);
        }
    }

    void VisitDecl(const Decl *d, bool) {
        logging::debug() << "Error: Unknown declaration kind \""
                         << d->getDeclKindName() << "\", dropping.\n";
    }

    void VisitBuiltinTemplateDecl(const BuiltinTemplateDecl *, bool) {
        // ignore
    }

    void VisitVarTemplateDecl(const VarTemplateDecl *decl, bool) {
        for (auto i : decl->specializations()) {
            this->Visit(i, true);
        }
    }

    void VisitStaticAssertDecl(const StaticAssertDecl *decl, bool) {
        module_.add_assert(decl);
    }

    void VisitAccessSpecDecl(const AccessSpecDecl *, bool) {
        // ignore
    }

    void VisitTranslationUnitDecl(const TranslationUnitDecl *decl, bool) {
        for (auto i : decl->decls()) {
            this->Visit(i, false);
        }
    }

    void VisitTypeDecl(const TypeDecl *type, bool) {
        logging::log() << "Error: Unsupported type declaration: "
                       << type->getQualifiedNameAsString()
                       << "(type = " << type->getDeclKindName() << ")\n";
    }

    void VisitEmptyDecl(const EmptyDecl *decl, bool) {}

    void VisitTypedefNameDecl(const TypedefNameDecl *type, bool) {
        go(type);
    }

    void VisitTagDecl(const TagDecl *decl, bool) {
        auto defn = decl->getDefinition();
        if (defn == decl) {
            go(decl, true);
        } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
            go(decl, false);
        }
    }

    void VisitCXXRecordDecl(const CXXRecordDecl *decl, bool is_specialization) {
        if (decl->isImplicit()) {
            return;
        }
        if (!is_specialization && isa<ClassTemplateSpecializationDecl>(decl)) {
            return;
        }

        // find any static functions or fields
        for (auto i : decl->decls()) {
            Visit(i, false);
        }

        VisitTagDecl(decl, false);
    }
    void VisitCXXMethodDecl(const CXXMethodDecl *decl, bool) {
        if (decl->isDeleted())
            return;
        this->ConstDeclVisitorArgs::VisitCXXMethodDecl(decl, false);
    }

    void VisitFunctionDecl(const FunctionDecl *decl, bool) {
        if (decl->isDependentContext()) {
            return;
        }

        using namespace comment;
        auto defn = decl->getDefinition();
        if (defn == decl) {
            if (auto c = context_->getRawCommentForDeclNoCache(decl)) {
                this->specs_.add_specification(decl, c, *context_);
            }

            if (go(decl, true) >= Filter::What::DEFINITION) {
                // search for static local variables
                for (auto i : decl->decls()) {
                    if (auto d = dyn_cast<VarDecl>(i)) {
                        if (d->isStaticLocal()) {
                            go(d);
                        }
                    }
                }
            }
        } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
            go(decl, false);
        }
    }

    void VisitEnumConstantDecl(const EnumConstantDecl *decl, bool) {
        go(decl);
    }

    void VisitVarDecl(const VarDecl *decl, bool) {
        if (not decl->isTemplated())
            go(decl);
    }

    void VisitFieldDecl(const FieldDecl *, bool) {
        // ignore
    }

    void VisitUsingDecl(const UsingDecl *, bool) {
        // ignore
    }

    void VisitUsingDirectiveDecl(const UsingDirectiveDecl *, bool) {
        // ignore
    }

    void VisitIndirectFieldDecl(const IndirectFieldDecl *, bool) {
        // ignore
    }

    void VisitNamespaceDecl(const NamespaceDecl *decl, bool) {
        for (auto d : decl->decls()) {
            this->Visit(d, false);
        }
    }

    void VisitEnumDecl(const EnumDecl *decl, bool) {
        if (not decl->isCanonicalDecl())
            return;
        go(decl);
        for (auto i : decl->enumerators()) {
            go(i);
        }
    }

    void VisitLinkageSpecDecl(const LinkageSpecDecl *decl, bool) {
        for (auto i : decl->decls()) {
            this->Visit(i, false);
        }
    }

    void VisitCXXConstructorDecl(const CXXConstructorDecl *decl, bool) {
        if (decl->isDeleted())
            return;

        this->ConstDeclVisitorArgs::VisitCXXConstructorDecl(decl, false);
    }

    void VisitCXXDestructorDecl(const CXXDestructorDecl *decl, bool) {
        if (decl->isDeleted())
            return;

        this->ConstDeclVisitorArgs::VisitCXXDestructorDecl(decl, false);
    }

    void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl, bool) {
        // note(gmm): for now, i am just going to return the specializations.
        for (auto i : decl->specializations()) {
            this->Visit(i, true);
        }
    }

    void VisitClassTemplateDecl(const ClassTemplateDecl *decl, bool) {
        for (auto i : decl->specializations()) {
            this->Visit(i, true);
        }
    }

    void VisitFriendDecl(const FriendDecl *decl, bool) {
        if (decl->getFriendDecl()) {
            this->Visit(decl->getFriendDecl(), true);
        }
    }

    void VisitTypeAliasTemplateDecl(const TypeAliasTemplateDecl *, bool) {}
    void VisitUsingShadowDecl(const UsingShadowDecl *, bool) {}
};

void
build_module(clang::TranslationUnitDecl *tu, ::Module &mod, Filter &filter,
             SpecCollector &specs, clang::CompilerInstance *ci,
             bool elaborate) {

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
        Elaborate(ci).VisitTranslationUnitDecl(tu, false);

        // Once we are done visiting the AST, we run all the actions that
        // are pending in the translation unit.
        // We need to do this because when we parse with elaboration enabled,
        // we parse in "incremental" mode. Ending the translation unit generates
        // all of the template specializations, etc.
        ci->getSema().ActOnEndOfTranslationUnit();
    }

    auto &ctxt = tu->getASTContext();
    BuildModule(mod, filter, &ctxt, specs, ci)
        .VisitTranslationUnitDecl(tu, false);
}

void ::Module::add_definition(const clang::NamedDecl *d, bool opaque) {
    if (opaque) {
        add_declaration(d);
    } else {
        definitions_.push_back(d);
#if 0
        auto found = definitions_.find(d);
        if (found == definitions_.end()) {
            definitions_.insert(d);
        } else {
            logging::debug() << "Error: Duplicate definition: "
                             << d->getQualifiedNameAsString() << "\n";
        }
#endif
    }
}

void ::Module::add_declaration(const clang::NamedDecl *d) {
    imports_.push_back(std::make_pair(d, true));
#if 0
    auto found = imports_.find(d);
    if (found == imports_.end()) {
        imports_.insert(std::make_pair(d, true));
    } else {
        logging::debug() << "Error: Duplicate declaration: "
                         << d->getQualifiedNameAsString() << "\n";
    }
#endif
}
