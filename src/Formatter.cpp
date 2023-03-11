/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "clang/Basic/LLVM.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/Support/raw_ostream.h"

#include "Formatter.hpp"

namespace fmt {

Formatter::Formatter() : Formatter(llvm::outs()) {}

Formatter::Formatter(llvm::raw_ostream& _out)
    : out(_out), depth(0), spaces(0), blank(true) {}

llvm::raw_ostream&
Formatter::line() {
    out << "\n";
    blank = true;
    spaces = 0;
    return out;
}

llvm::raw_ostream&
Formatter::nobreak() {
    if (blank) {
        for (unsigned int d = this->depth; d > 0; --d) {
            out << " ";
        }
        blank = false;
    }
    while (spaces > 0) {
        out << " ";
        spaces--;
    }
    return out;
}

void
Formatter::nbsp() {
    spaces++;
}

void
Formatter::indent() {
    this->depth += 2;
}
void
Formatter::outdent() {
    assert(this->depth >= 2);
    this->depth -= 2;
}

void
Formatter::ascii(int val) {
    out << "\"";
    out << (char)((val >> 6) + '0');
    out << (char)(((val >> 3) & 0x7) + '0');
    out << (char)((val & 0x7) + '0');
    out << "\"";
}

Formatter Formatter::default_output = Formatter();

struct NBSP;
const NBSP* nbsp;

Formatter&
operator<<(Formatter& out, const NBSP* _) {
    out.nbsp();
    return out;
}

struct INDENT;
const INDENT* indent;

Formatter&
operator<<(Formatter& out, const INDENT* _) {
    out.indent();
    return out;
}

struct OUTDENT;
const OUTDENT* outdent;

Formatter&
operator<<(Formatter& out, const OUTDENT* _) {
    out.outdent();
    return out;
}

struct LPAREN;
const LPAREN* lparen;
Formatter&
operator<<(Formatter& out, const LPAREN* _) {
    out.nobreak() << "(";
    out.indent();
    return out;
}

struct RPAREN;
const RPAREN* rparen;
Formatter&
operator<<(Formatter& out, const RPAREN* _) {
    out.outdent();
    out.nobreak() << ")";
    return out;
}

struct LINE;
const LINE* line;
Formatter&
operator<<(Formatter& out, const LINE* _) {
    out.line();
    return out;
}

Formatter&
operator<<(Formatter& out, BOOL b) {
    out.nobreak() << (b.value ? "true" : "false");
    return out;
}

Formatter&
operator<<(Formatter& out, const llvm::APSInt& val) {
    out.nobreak() << "(";
    val.print(out.nobreak(), val.isSigned());
    out.nobreak() << ")%Z";
    return out;
}
}