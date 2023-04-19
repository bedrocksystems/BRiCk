/*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "Formatter.hpp"
#include "FromClang.hpp"
#include "Logging.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"
#include "ToCoq.hpp"
#include "clang/Basic/Builtins.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include <set>

using namespace clang;

static void
unsupported_decl(const Decl *decl) {
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
    bool recursive_;

public:
    Elaborate(clang::CompilerInstance *ci, bool templates, bool rec = false)
        : ci_(ci), templates_(templates), recursive_(rec) {}

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

    void VisitTranslationUnitDecl(const TranslationUnitDecl *decl,
                                  Flags flags) {
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
        if (isa<ClassTemplatePartialSpecializationDecl>(decl)) {
            return;
        }

        if (decl->isCompleteDefinition()) {
            // Do *not* generate deprecated members
            GenerateImplicitMembers(decl, false);
        }

        if (recursive_) {
            // find any static functions or fields
            for (auto i : decl->decls()) {
                Visit(i, flags);
            }
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

        // this->DeclVisitorArgs::VisitCXXConstructorDecl(decl, flags);
    }

    void VisitCXXDestructorDecl(CXXDestructorDecl *decl, Flags) {
        if (decl->isDeleted())
            return;

        if (not decl->hasBody() && decl->isDefaulted()) {
            ci_->getSema().DefineImplicitDestructor(decl->getLocation(), decl);
        }
    }

    void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl,
                                   Flags flags) {
#if 0
        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
#endif
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
    void VisitFunctionDecl(const FunctionDecl *, Flags) {}
};

void
ToCoqConsumer::elab(Decl *d, bool rec) {
    Flags f{false, false};
    if (auto dc = dyn_cast<DeclContext>(d)) {
        f.in_template = dc->isDependentContext();
    }
    if (not f.in_template) {
        Elaborate(compiler_, templates_file_.has_value(), rec).Visit(d, f);
    }
}

bool
ToCoqConsumer::HandleTopLevelDecl(DeclGroupRef decl) {
    if (elaborate_) {
        for (auto i : decl) {
            elab(i, true);
        }
    }
    return true;
}

void
ToCoqConsumer::HandleCXXImplicitFunctionInstantiation(FunctionDecl *decl) {
    elab(decl);
}

void
ToCoqConsumer::HandleInlineFunctionDefinition(FunctionDecl *decl) {
    elab(decl);
}

void
ToCoqConsumer::HandleTagDeclDefinition(TagDecl *decl) {
    if (elaborate_) {
        elab(decl);
    }
#if 0
    if (auto cxxrd = dyn_cast<CXXRecordDecl>(decl)) {
        Sema &sema = compiler_->getSema();
        if (true) {
            sema.ForceDeclarationOfImplicitMembers(cxxrd);
        } else
            GenerateUndeprecatedImplicitMembers(cxxrd, sema);

        for (auto c : cxxrd->ctors()) {
            if (c->isDeleted())
                continue;
            if (not c->getBody() && c->isDefaulted()) {
                if (c->isDefaultConstructor()) {
                    sema.DefineImplicitDefaultConstructor(c->getLocation(), c);
                } else if (c->isCopyConstructor()) {
                    sema.DefineImplicitCopyConstructor(c->getLocation(), c);
                } else if (c->isMoveConstructor()) {
                    sema.DefineImplicitMoveConstructor(c->getLocation(), c);
                } else {
                    logging::debug() << "Unknown defaulted constructor.\n";
                }
            }
        }

        for (auto m : cxxrd->methods()) {
            llvm::errs() << "Method: " << m->getNameAsString() << "\n";
            if (m->isDeleted())
                continue;

            if (not m->getBody() && m->isDefaulted()) {
                if (m->isMoveAssignmentOperator()) {
                    sema.DefineImplicitMoveAssignment(m->getLocation(), m);

                } else if (m->isCopyAssignmentOperator()) {
                    sema.DefineImplicitCopyAssignment(m->getLocation(), m);
                } else {
                    logging::log()
                        << "Didn't generate body for defaulted method\n";
                }
            }
        }
    }
#endif
}
