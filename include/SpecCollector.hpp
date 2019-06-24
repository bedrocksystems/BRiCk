/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include <utility>
#include <map>

#include "clang/AST/Decl.h"

class SpecCollector {
public:
	void add_specification(const clang::Decl* decl, clang::StringRef ref) {
		this->specifications_.push_back(std::make_pair(decl, ref));
	}

	std::list<std::pair<const clang::Decl*, clang::StringRef> >::const_iterator
	begin() const {
		return this->specifications_.begin();
	}

	std::list<std::pair<const clang::Decl*, clang::StringRef> >::const_iterator
	end() const {
		return this->specifications_.end();
	}

private:
	std::list<std::pair<const clang::Decl*, clang::StringRef> > specifications_;
};
