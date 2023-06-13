/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

namespace things { int x; }

int test() {
    using namespace things;
    return x;
}
