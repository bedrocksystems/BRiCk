/*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

#pragma once
#include <optional>

namespace clang {
class Decl;
class NamedDecl;
class TemplateDecl;
class TemplateArgumentList;
}

/// Shallow view of template specialization
struct SDecl {
	const clang::TemplateDecl &temp;
	const clang::TemplateArgumentList &args;

	SDecl() = delete;
	SDecl(const clang::TemplateDecl &t, const clang::TemplateArgumentList &a)
		: temp{t}, args{a} {}
};
using SDeclO = std::optional<SDecl>;

/**
Attempt to decompose a declaration _directly_ into a template applied to
arguments. This does not account for "untemplated" declarations in
templated scopes.
*/
SDeclO recoverSpecialization(const clang::Decl &);
