/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 */
#pragma once
#include <clang/AST/Decl.h>
#include <list>
#include <map>
#include <utility>
namespace clang {
class CompilerInstance;
};

class Module {
public:
    void add_definition(clang::NamedDecl* d, bool opaque = false);

    void add_declaration(clang::NamedDecl* d);

    const std::multimap<std::string, std::pair<clang::NamedDecl*, bool>>&
    imports() const {
        return imports_;
    }

    const std::multimap<std::string, clang::NamedDecl*>& definitions() const {
        return definitions_;
    }

    Module() : imports_(), definitions_() {}

private:
    std::multimap<std::string, std::pair<clang::NamedDecl*, bool>> imports_;
    std::multimap<std::string, clang::NamedDecl*> definitions_;
};

class Filter;
class SpecCollector;

void build_module(clang::TranslationUnitDecl* tu, ::Module& mod, Filter& filter,
                  SpecCollector& specs, clang::CompilerInstance*,
                  bool elaborate = true);
