/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include "CommentScanner.hpp"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"

using namespace clang;

class BuildModule : public ConstDeclVisitorArgs<BuildModule, void, bool> {
private:
    ::Module &module_;
    Filter &filter_;
    SpecCollector &specs_;
    clang::ASTContext *const context_;

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
                SpecCollector &specs)
        : module_(m), filter_(filter), specs_(specs), context_(context) {}

    void VisitDecl(const Decl *d, bool) {
        logging::log() << "visiting declaration..." << d->getDeclKindName()
                       << "\n";
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

    void VisitFunctionDecl(const FunctionDecl *decl, bool) {
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
        if (decl->getName() != "") {
            go(decl);
        }
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
        if (decl->isDeleted()) {
            return;
        }
        this->ConstDeclVisitorArgs::VisitCXXConstructorDecl(decl, false);
    }

    void VisitCXXDestructorDecl(const CXXDestructorDecl *decl, bool) {
        if (decl->isDeleted()) {
            return;
        }
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
};

void
build_module(const clang::TranslationUnitDecl *tu, ::Module &mod,
             Filter &filter, SpecCollector &specs) {
    auto &ctxt = tu->getASTContext();
    BuildModule(mod, filter, &ctxt, specs).VisitTranslationUnitDecl(tu, false);
}

void ::Module::add_definition(const clang::NamedDecl *d, bool opaque) {
    if (opaque) {
        add_declaration(d);
    } else {
        std::string name = d->getNameAsString();
        auto found = definitions_.find(name);
        if ((found == definitions_.end()) || found->second != d) {
            definitions_.insert(std::make_pair(name, d));
        }
    }
}

void ::Module::add_declaration(const clang::NamedDecl *d) {
    std::string name = d->getNameAsString();
    auto found = imports_.find(name);
    if ((found == imports_.end()) || found->second.first != d) {
        imports_.insert(std::make_pair(name, std::make_pair(d, true)));
    }
}
