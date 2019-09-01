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
    void add_definition(const clang::NamedDecl* d, bool opaque = false) {
        if (opaque) {
            add_declaration(d);
        } else {
            llvm::StringRef name = d->getNameAsString();
            auto found = definitions_.find(name);
            if ((found == definitions_.end()) || found->second != d) {
                definitions_.insert(std::make_pair(name, d));
            }
        }
    }

    void add_declaration(const clang::NamedDecl* d) {
        llvm::StringRef name = d->getNameAsString();
        auto found = imports_.find(name);
        if ((found == imports_.end()) || found->second.first != d) {
            imports_.insert(std::make_pair(name, std::make_pair(d, true)));
        }
    }

    const std::multimap<clang::StringRef,
                        std::pair<const clang::NamedDecl*, bool>>&
    imports() const {
        return imports_;
    }

    const std::multimap<clang::StringRef, const clang::NamedDecl*>&
    definitions() const {
        return definitions_;
    }

    Module() : imports_(), definitions_() {}

private:
    std::multimap<clang::StringRef, std::pair<const clang::NamedDecl*, bool>>
        imports_;
    std::multimap<clang::StringRef, const clang::NamedDecl*> definitions_;
};

class Filter;
class SpecCollector;

void build_module(const clang::TranslationUnitDecl* tu, ::Module& mod,
                  Filter& filter, SpecCollector& specs);
