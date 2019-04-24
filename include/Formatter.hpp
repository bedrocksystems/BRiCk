/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#pragma once

#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringRef.h"
#include <string.h>

namespace fmt {

class Formatter {
private:
	llvm::raw_ostream &out;
	unsigned int depth;
	unsigned int spaces;
	bool blank;

public:
	explicit
	Formatter();
	explicit
	Formatter(llvm::raw_ostream&);

	llvm::raw_ostream&
	line();

	llvm::raw_ostream&
	nobreak();

	void
	nbsp();

	void
	indent();
	void
	outdent();

	void
	ascii(int c);

	llvm::raw_ostream&
	error() const;

	template<typename T>
	Formatter& operator<<(T val) {
		nobreak() << val;
		blank = false;
		return *this;
	}

public:
	static Formatter default_output;
};

struct NBSP;
extern const NBSP* nbsp;

Formatter&
operator<<(Formatter &out, const NBSP *_);

struct INDENT;
extern const INDENT* indent;

Formatter&
operator<<(Formatter &out, const INDENT *_);

struct OUTDENT;
extern const OUTDENT* outdent;

Formatter&
operator<<(Formatter &out, const OUTDENT *_);

struct LPAREN;
extern const LPAREN* lparen;

Formatter&
operator<<(Formatter &out, const LPAREN *_);

struct RPAREN;
extern const RPAREN* rparen;

struct LINE;
extern const LINE* line;
Formatter&
operator<<(Formatter &out, const LINE *_);

Formatter&
operator<<(Formatter &out, const RPAREN *_);

}

