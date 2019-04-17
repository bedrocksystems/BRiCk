#pragma once
#include <list>
#include <utility>
#include <map>
#include <clang/AST/Decl.h>

class Module {


public:
  void add_definition(const clang::NamedDecl* d, bool opaque=false) {
    if (opaque) {
      add_declaration(d);
    } else {
      definitions_.insert(std::make_pair(d->getName(), d));
    }
  }
  void add_declaration(const clang::NamedDecl* d) {
    imports_.insert(std::make_pair(d->getName(), std::make_pair(d, true)));
  }

  const std::multimap<clang::StringRef, std::pair<const clang::NamedDecl*, bool> >& imports() const {
    return imports_;
  }

  const std::multimap<clang::StringRef, const clang::NamedDecl*>& definitions() const {
    return definitions_;
  }

  Module():imports_(),definitions_() {}

private:
  std::multimap<clang::StringRef, std::pair<const clang::NamedDecl*, bool> > imports_;
  std::multimap<clang::StringRef, const clang::NamedDecl*> definitions_;
};

class Filter;

void build_module(const clang::TranslationUnitDecl* tu, ::Module &mod, Filter &f);