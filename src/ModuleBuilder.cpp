#include "DeclVisitorWithArgs.h"
#include "ModuleBuilder.hpp"
#include "Filter.hpp"

using namespace clang;

class BuildModule : public ConstDeclVisitorArgs<BuildModule, void> {
  private:
  ::Module& module_;
  Filter& filter_;

private:
  Filter::What go(const NamedDecl* decl, bool definition=true) {
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
  BuildModule(::Module& m, Filter& filter):module_(m),filter_(filter) {}

  void VisitDecl(const Decl *d)
  {
    llvm::errs() << "visiting declaration..." << d->getDeclKindName() << "\n";
  }

  void VisitAccessSpecDecl(const AccessSpecDecl*) {
    // ignore
  }

  void VisitTranslationUnitDecl(const TranslationUnitDecl* decl) {
    for (auto i : decl->decls()) {
      this->Visit(i);
    }
  }

  void VisitTypeDecl(const TypeDecl *type)
  {
    llvm::errs() << "unsupported type declaration `" << type->getDeclKindName() << "`\n";
  }

  void VisitEmptyDecl(const EmptyDecl *decl) {}

  void VisitTypedefNameDecl(const TypedefNameDecl *type)
  {
    go(type);
  }

  void VisitTagDecl(const TagDecl* decl) {
    auto defn = decl->getDefinition();
    if (defn == decl) {
      go(decl, true);
    } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
      go(decl, false);
    }
  }

  void VisitCXXRecordDecl(const CXXRecordDecl* decl) {
    // find any static functions or fields
    for (auto i : decl->decls()) {
      Visit(i);
    }

    VisitTagDecl(decl);
  }

  void VisitFunctionDecl(const FunctionDecl *decl)
  {
    auto defn = decl->getDefinition();
    if (defn == decl) {
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

  void VisitEnumConstantDecl(const EnumConstantDecl *decl) {
    go(decl);
  }

  void VisitVarDecl(const VarDecl *decl) {
    go(decl);
  }

  void VisitFieldDecl(const FieldDecl*) {
    // ignore
  }

  void VisitUsingDecl(const UsingDecl *) {
    // ignore
  }

  void VisitUsingDirectiveDecl(const UsingDirectiveDecl *) {
    // ignore
  }

  void VisitIndirectFieldDecl(const IndirectFieldDecl *) {
    // ignore
  }

  void VisitNamespaceDecl(const NamespaceDecl *decl)
  {
    for (auto d : decl->decls()) {
      this->Visit(d);
    }
  }

  void VisitEnumDecl(const EnumDecl *decl)
  {
    if (decl->getName() != "") {
      go(decl);
    }
    for (auto i : decl->enumerators()) {
      go(i);
    }
  }

  void VisitLinkageSpecDecl(const LinkageSpecDecl *decl)
  {
    for (auto i : decl->decls()) {
      this->Visit(i);
    }
  }

  void VisitCXXConstructorDecl(const CXXConstructorDecl *decl) {
    if (decl->isDeleted()) {
      return;
    }
    this->ConstDeclVisitorArgs::VisitCXXConstructorDecl(decl);
  }

  void VisitCXXDestructorDecl(const CXXDestructorDecl *decl) {
    if (decl->isDeleted()) {
      return;
    }
    this->ConstDeclVisitorArgs::VisitCXXDestructorDecl(decl);
  }

  void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl)
  {
    // note(gmm): for now, i am just going to return the specializations.
    for (auto i : decl->specializations()) {
      this->Visit(i);
    }
  }

  void VisitClassTemplateDecl(const ClassTemplateDecl *decl)
  {
    for (auto i : decl->specializations()) {
      this->Visit(i);
    }
  }
};


void build_module(const clang::TranslationUnitDecl* tu, ::Module &mod, Filter& filter) {
  BuildModule(mod, filter).VisitTranslationUnitDecl(tu);
}