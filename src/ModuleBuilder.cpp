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

class BuildModule : public DeclVisitorArgs<BuildModule, void, bool> {
private:
    ::Module &module_;
    Filter &filter_;
    SpecCollector &specs_;
    clang::ASTContext *const context_;
    clang::CompilerInstance *const ci_;
    bool elaborate_;
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
                SpecCollector &specs, clang::CompilerInstance *ci,
                bool elab = true)
        : module_(m), filter_(filter), specs_(specs), context_(context),
          ci_(ci), elaborate_(elab) {}

    void Visit(Decl *d, bool s) {
        if (visited_.find(d->getID()) == visited_.end()) {
            visited_.insert(d->getID());
            DeclVisitorArgs<BuildModule, void, bool>::Visit(d, s);
        }
    }

    void VisitDecl(const Decl *d, bool) {
        logging::debug() << "Unknown declaration kind \""
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
        logging::log() << "unsupported type declaration `"
                       << type->getDeclKindName() << "`\n";
    }

    void VisitEmptyDecl(EmptyDecl *decl, bool) {}

    void VisitTypedefNameDecl(TypedefNameDecl *type, bool) {
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

    void VisitCXXRecordDecl(CXXRecordDecl *decl, bool is_specialization) {
        if (decl->isImplicit()) {
            return;
        }
        if (!is_specialization && isa<ClassTemplateSpecializationDecl>(decl)) {
            return;
        }

        if (elaborate_) {
            if (not(decl->isImplicit() /* or decl->isAnonymousStructOrUnion() */)) {
                ci_->getSema().ForceDeclarationOfImplicitMembers(decl);
            }
        }

        // find any static functions or fields
        for (auto i : decl->decls()) {
            Visit(i, false);
        }

        VisitTagDecl(decl, false);
    }
    void VisitCXXMethodDecl(CXXMethodDecl *decl, bool) {
        if (decl->isDeleted() or decl->isDependentContext())
            return;

        if (elaborate_) {
            if (not decl->getBody() && decl->isDefaulted()) {
                if (decl->isMoveAssignmentOperator()) {
                    ci_->getSema().DefineImplicitMoveAssignment(
                        decl->getLocation(), decl);

                } else if (decl->isCopyAssignmentOperator()) {
                    ci_->getSema().DefineImplicitCopyAssignment(
                        decl->getLocation(), decl);
                } else {
                    logging::log()
                        << "Didn't generate body for defaulted method\n";
                }
            }
        }

        go(decl);
    }

    void VisitFunctionDecl(const FunctionDecl *decl, bool) {
        if (decl->isDependentContext())
            return;

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

    void VisitCXXConstructorDecl(CXXConstructorDecl *decl, bool) {
        if (decl->isDeleted()) {
            return;
        }
        if (elaborate_) {
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
        }

        this->DeclVisitorArgs::VisitCXXConstructorDecl(decl, false);
    }

    void VisitCXXDestructorDecl(CXXDestructorDecl *decl, bool) {
        if (decl->isDeleted())
            return;

        if (elaborate_) {
            if (not decl->hasBody() && decl->isDefaulted()) {
                ci_->getSema().DefineImplicitDestructor(decl->getLocation(),
                                                        decl);
            }
        }
        this->DeclVisitorArgs::VisitCXXDestructorDecl(decl, false);
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
    auto &ctxt = tu->getASTContext();

    BuildModule(mod, filter, &ctxt, specs, ci, elaborate)
        .VisitTranslationUnitDecl(tu, false);
    // Once we are done visiting the AST, we run all the actions that
    // are pending in the translation unit.
    ci->getSema().ActOnEndOfTranslationUnit();
}

void ::Module::add_definition(const clang::NamedDecl *d, bool opaque) {
    if (opaque) {
        add_declaration(d);
    } else {
        auto found = definitions_.find(d);
        if (found != definitions_.end()) {
            logging::debug()
                << "duplicate definition: " << d->getQualifiedNameAsString()
                << "\n";
        } else {
            definitions_.insert(d);
        }
    }
}

void ::Module::add_declaration(const clang::NamedDecl *d) {
    auto found = imports_.find(d);
    if (found == imports_.end()) {
        imports_.insert(std::make_pair(d, true));
    } else {
        logging::debug() << "duplicate declaration: "
                         << d->getQualifiedNameAsString() << "\n";
    }
}
