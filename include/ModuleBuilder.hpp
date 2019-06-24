/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
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
      definitions_.insert(std::make_pair(llvm::StringRef(d->getNameAsString()), d));
    }
  }

  void add_declaration(const clang::NamedDecl* d) {
    imports_.insert(std::make_pair(llvm::StringRef(d->getNameAsString()), std::make_pair(d, true)));
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
