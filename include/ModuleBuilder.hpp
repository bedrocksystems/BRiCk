/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <list>
#include <map>
#include <set>
#include <utility>

namespace clang {
class CompilerInstance;
};

class Module {
public:
    void add_definition(const clang::NamedDecl* d, bool opaque = false);

    void add_declaration(const clang::NamedDecl* d);

    void add_assert(const clang::StaticAssertDecl* d) {
        asserts_.push_back(d);
    }

    const auto& asserts() const {
        return asserts_;
    }

    const auto& imports() const {
        return imports_;
    }

    const auto& definitions() const {
        return definitions_;
    }

    Module() : imports_(), definitions_() {}

private:
    std::list<std::pair<const clang::NamedDecl*, bool>> imports_;
    std::list<const clang::NamedDecl*> definitions_;

    std::list<const clang::StaticAssertDecl*> asserts_;
};

class Filter;
class SpecCollector;

void build_module(clang::TranslationUnitDecl* tu, ::Module& mod, Filter& filter,
                  SpecCollector& specs, clang::CompilerInstance*,
                  bool elaborate = true);
