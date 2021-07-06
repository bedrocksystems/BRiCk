/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
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
    void add_definition(const clang::NamedDecl* d, bool opaque = false);

    void add_declaration(const clang::NamedDecl* d);

    const std::multimap<std::string, std::pair<const clang::NamedDecl*, bool>>&
    imports() const {
        return imports_;
    }

    const std::multimap<std::string, const clang::NamedDecl*>&
    definitions() const {
        return definitions_;
    }

    Module() : imports_(), definitions_() {}

private:
    std::multimap<std::string, std::pair<const clang::NamedDecl*, bool>>
        imports_;
    std::multimap<std::string, const clang::NamedDecl*> definitions_;
};

class Filter;
class SpecCollector;

void build_module(clang::TranslationUnitDecl* tu, ::Module& mod, Filter& filter,
                  SpecCollector& specs, clang::CompilerInstance*,
                  bool elaborate = true);
