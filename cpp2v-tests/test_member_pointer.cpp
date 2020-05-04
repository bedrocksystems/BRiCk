/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

struct P {
    int x;
};

int test() {
    auto t = &P::x;
    P x;
    return x.*t;
}
