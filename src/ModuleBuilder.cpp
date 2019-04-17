#include "DeclVisitorWithArgs.h"
#include "ModuleBuilder.hpp"
#include "Filter.hpp"

using namespace clang;

class BuildModule : public ConstDeclVisitorArgs<BuildModule, void> {
  private:
  ::Module& module_;
  Filter& filter_;

private:
  void go(const NamedDecl* decl, bool definition=true) {
    switch (filter_.shouldInclude(decl)) {
    case Filter::What::DEFINITION:
      if (definition) {
        module_.add_definition(decl);
      } else {
        module_.add_declaration(decl);
      }
      break;
    case Filter::What::DECLARATION:
      module_.add_declaration(decl);
      break;
    default:
      break;
    }
  }

public:
  BuildModule(::Module& m, Filter& filter):module_(m),filter_(filter) {}

  void VisitDecl(const Decl *d)
  {
    llvm::errs() << "visiting declaration..." << d->getDeclKindName() << "\n";
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
    llvm::errs() << decl->getName() << ": "
                 << decl << " "
                 << decl->getDefinition() << " "
                 << decl->getPreviousDecl() << " "
                 << decl->isThisDeclarationADefinition() << "\n";
    auto defn = decl->getDefinition();
    if (defn == decl) {
      go(decl, true);
    } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
      go(decl, false);
    } else {
      llvm::errs() << "skipping";
    }
  }

  void VisitFunctionDecl(const FunctionDecl *decl)
  {
    auto defn = decl->getDefinition();
    if (defn == decl) {
      go(decl, true);
    } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
      go(decl, false);
    }
  }

  void VisitEnumConstantDecl(const EnumConstantDecl *decl) {
    go(decl);
  }

  void VisitVarDecl(const VarDecl *decl)
  {
    go(decl);
  }

  void VisitUsingDecl(const UsingDecl *decl)
  {
    // ignore
  }

  void VisitUsingDirectiveDecl(const UsingDirectiveDecl *decl)
  {
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
    go(decl);
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