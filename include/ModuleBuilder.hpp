#pragma once
#include <list>
#include <utility>
#include <map>
#include <clang/AST/Decl.h>

class Module {
public:
  void add_definition(const clang::NamedDecl* d, bool opaque=false) {
    if (opaque) {
      this->add_declaration(d);
    } else {
      this->definitions_.insert(std::make_pair(d->getName(), d));
      this->imports_.erase(d->getName());
    }
  }
  void add_declaration(const clang::NamedDecl* d) {
    auto loc = this->imports_.find(d->getName());
    if (loc != this->imports_.end()) {
      auto thing = loc->second;
      llvm::errs() << "replacing: " << thing.first << " (canonical = " << thing.first->getCanonicalDecl() << ") with "
                   << d << " (canonical = " << d->getCanonicalDecl() << ")\n";
      this->imports_.insert(std::make_pair(d->getName(), std::make_pair(d, true)));
    } else {
      this->imports_.insert(std::make_pair(d->getName(), std::make_pair(d, true)));
    }
  }

  const std::map<clang::StringRef, std::pair<const clang::NamedDecl*, bool> >& imports() const {
    return this->imports_;
  }

  const std::map<clang::StringRef, const clang::NamedDecl*>& definitions() const {
    return this->definitions_;
  }

  Module():imports_(),definitions_() {}

private:
  std::map<clang::StringRef, std::pair<const clang::NamedDecl*, bool> > imports_;
  std::map<clang::StringRef, const clang::NamedDecl*> definitions_;
};

class Filter;

void build_module(const clang::TranslationUnitDecl* tu, ::Module &mod, Filter &f);