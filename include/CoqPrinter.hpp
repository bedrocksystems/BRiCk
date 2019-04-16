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
	CoqPrinter() = default;

	fmt::Formatter& ctor(const char* ctor, bool line=true);
	fmt::Formatter& begin_record(bool line=true);
	fmt::Formatter& end_record(bool line=true);
	fmt::Formatter& record_field(const char* field, bool line=true);

	fmt::Formatter& some();
	fmt::Formatter& none();

public:
	fmt::Formatter& output();
	llvm::raw_ostream& error () const;
};