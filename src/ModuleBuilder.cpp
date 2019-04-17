#include "DeclVisitorWithArgs.h"
#include "ModuleBuilder.hpp"
#include "Filter.hpp"

using namespace clang;

class BuildModule : public ConstDeclVisitorArgs<BuildModule, void> {
  private:
  ::Module& module_;
  Filter& filter_;

private:
  void go(const NamedDecl* decl) {
    switch (filter_.shouldInclude(decl)) {
    case Filter::What::DEFINITION:
      module_.add_definition(decl);
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
    module_.add_definition(type);
  }

  void VisitCXXRecordDecl(const CXXRecordDecl *decl)
  {
    if (decl->isCompleteDefinition()) {
      module_.add_definition(decl);
    } else {
      module_.add_declaration(decl);
    }
  }

  void VisitFunctionDecl(const FunctionDecl *decl)
  {
    module_.add_definition(decl);
  }

  void VisitEnumConstantDecl(const EnumConstantDecl *decl) {
    module_.add_definition(decl);
  }

  void VisitVarDecl(const VarDecl *decl)
  {
    module_.add_definition(decl);
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
    module_.add_definition(decl);
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
    //print.ctor("Dtemplated");

    /*
			 print.output() << "(";
			 for (auto i = decl->getTemplateParameters()->begin(), e = decl->getTemplateParameters()->end(); i != e; ++i) {
			 if (auto *nt = dyn_cast<NonTypeTemplateParmDecl>(*i)) {
			 print.output() << "(NotType" << fmt::nbsp;
			 cprint.printQualType(nt->getType());
			 print.output() << ",\"" << (*i)->getNameAsString() << "\") ::" << fmt::nbsp;
			 } else if (isa<TemplateTypeParmDecl>(*i)) {
			 print.output() << "(Typename, \"" << (*i)->getNameAsString() << "\") ::" << fmt::nbsp;
			 } else {
			 print.error() << "[ERR] unsupported template parameter type " << (*i)->getDeclKindName() << "\n";
			 }
			 }
			 print.output() << "nil)";

			 cprint.printDecl(decl->getTemplatedDecl());
			 print.output() << fmt::nbsp;
			 */

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