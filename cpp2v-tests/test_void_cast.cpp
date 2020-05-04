/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

void test(void* p) {
    int* si = static_cast<int*>(p);
    int* ri = reinterpret_cast<int*>(p);
}
