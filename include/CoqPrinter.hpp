// Copyright (C) 2019 BedRock Systems
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "Formatter.hpp"
#include "llvm/ADT/StringRef.h"

class CoqPrinter {
public:
    CoqPrinter(fmt::Formatter& output) : output_(output) {}

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

    fmt::Formatter& str(const char* str) {
        return this->output_ << "\"" << str << "\"";
    }
    fmt::Formatter& str(llvm::StringRef str) {
        return this->output_ << "\"" << str << "\"";
    }

    fmt::Formatter& boolean(bool b) {
        return this->output_ << (b ? "true" : "false");
    }

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
    fmt::Formatter& output() {
        return this->output_;
    }

private:
    fmt::Formatter& output_;
};