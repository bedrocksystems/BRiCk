/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#pragma once
#include <clang/AST/Decl.h>
#include <list>
#include <map>
#include <utility>

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

void build_module(const clang::TranslationUnitDecl* tu, ::Module& mod,
                  Filter& filter, SpecCollector& specs);
