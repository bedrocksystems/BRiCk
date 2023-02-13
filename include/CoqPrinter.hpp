/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "Formatter.hpp"
#include <clang/AST/Expr.h>
#include <llvm/ADT/StringRef.h>

class CoqPrinter {
public:
    CoqPrinter(fmt::Formatter& output, bool templates) : output_(output), templates_(templates) {}

    bool templates() const { return templates_; }

    fmt::Formatter& type() {
        return this->output_ << (templates() ? "Mtype" : "type");
    }

    fmt::Formatter& begin_tuple() {
        return this->output_ << "(";
    }
    fmt::Formatter& end_tuple() {
        return this->output_ << ")";
    }
    fmt::Formatter& next_tuple() {
        return this->output_ << "," << fmt::nbsp;
    }

    fmt::Formatter& ctor(const char* ctor, bool line = true) {
        if (line) {
            this->output_ << fmt::line;
        }
        return this->output_ << fmt::lparen << ctor << fmt::nbsp;
    }
    fmt::Formatter& end_ctor() {
        return this->output_ << fmt::rparen;
    }
    fmt::Formatter& begin_record(bool line = true) {
        if (line) {
            this->output_ << fmt::line;
        }
        return this->output_ << "{|" << fmt::nbsp;
    }
    fmt::Formatter& end_record(bool line = true) {
        if (line) {
            this->output_ << fmt::line;
        }
        return this->output_ << fmt::nbsp << "|}";
    }
    fmt::Formatter& record_field(const char* field, bool line = true) {
        return this->output_ << field << fmt::nbsp << ":=" << fmt::nbsp;
    }

    fmt::Formatter& some() {
        return this->ctor("Some");
    }
    fmt::Formatter& none() {
        return this->output_ << "None";
    }

    fmt::Formatter& ascii(int c) {
        assert(0 <= c && c < 256);
        this->output_.ascii(c);
        return this->output_;
    }

    /** Print a "plain" string (no special characters) */
    fmt::Formatter& str(const char* str) {
        return this->output_ << "\"" << str << "\"";
    }

    /** Print a "complex" string (special characters will be escaped) */
    fmt::Formatter& escaped_str(const clang::StringLiteral* lit);

    fmt::Formatter& str(llvm::StringRef str) {
        return this->output_ << "\"" << str << "\"";
    }

    fmt::Formatter& boolean(bool b) {
        return this->output_ << (b ? "true" : "false");
    }

    // List-printing functions
    template<typename I, typename CLOSURE>
    fmt::Formatter& list_range(I begin, I end, CLOSURE fn) {
        if (begin == end) {
            return this->output_ << "nil";
        }
        begin_list();
        while (begin != end) {
            fn(*this, *begin);
            cons();
            ++begin;
        }
        return end_list();
    }

    template<typename C, typename CLOSURE>
    fmt::Formatter& list(const C &&list, CLOSURE fn) {
        return list_range(list.begin(), list.end(), fn);
    }

    // List-printing functions
    template<typename I, typename CLOSURE>
    fmt::Formatter& list_range_filter(I begin, I end, CLOSURE fn) {
        if (begin == end) {
            return this->output_ << "nil";
        }
        begin_list();
        while (begin != end) {
            if (fn(*this, *begin))
                cons();
            ++begin;
        }
        return end_list();
    }

    template<typename C, typename CLOSURE>
    fmt::Formatter& list_filter(const C &&list, CLOSURE fn) {
        return list_range_filter(list.begin(), list.end(), fn);
    }

    // low-level list-printing API
    fmt::Formatter& begin_list() {
        return this->output_ << fmt::lparen;
    }
    fmt::Formatter& end_list() {
        return this->output_ << "nil" << fmt::rparen;
    }
    fmt::Formatter& cons() {
        return this->output_ << fmt::nbsp << "::" << fmt::nbsp;
    }

public:
    fmt::Formatter& output() const {
        return this->output_;
    }

private:
    fmt::Formatter& output_;
    const bool templates_;
};
