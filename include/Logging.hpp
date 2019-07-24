/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
namespace llvm {
	class raw_ostream;
};

namespace logging {
	enum Level : int {
		FATAL       = -1,
		NONE        = 0,
		UNSUPPORTED = 5,
		VERBOSE     = 10,
		VERBOSER    = 20,
		ALL         = 1000,
	};

	llvm::raw_ostream& log(Level level=VERBOSE);

	static inline llvm::raw_ostream& fatal() { return log(FATAL); }
	static inline llvm::raw_ostream& unsupported() { return log(UNSUPPORTED); }

	void set_level(Level level);

	[[noreturn]]
	void die();
}