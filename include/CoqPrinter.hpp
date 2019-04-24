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

class CoqPrinter {
public:
	CoqPrinter(fmt::Formatter& output):output_(output) {}

	fmt::Formatter& ctor(const char* ctor, bool line=true) {
		if (line) {
			this->output_ << fmt::line;
		}
		this->output_ << fmt::lparen << ctor << fmt::nbsp;
		return this->output_;
	}
	fmt::Formatter& begin_record(bool line=true) {
		if (line) {
			this->output_ << fmt::line;
		}
		this->output_ << "{|" << fmt::nbsp;
		return this->output_;
	}
	fmt::Formatter& end_record(bool line=true) {
		if (line) {
			this->output_ << fmt::line;
		}
		this->output_ << fmt::nbsp << "|}";
		return this->output_;
	}
	fmt::Formatter& record_field(const char* field, bool line=true) {
		this->output_ << field << fmt::nbsp << ":=" << fmt::nbsp;
		return this->output_;
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

public:
	fmt::Formatter& output() {
		return this->output_;
	}
	llvm::raw_ostream& error () const {
		return llvm::errs();
	}

private:
	fmt::Formatter& output_;
};