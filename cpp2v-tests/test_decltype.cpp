/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

int test() {
    int x = 0;
    decltype(x) y = 3;
    decltype((x)) z = x;
#if __cplusplus < 201700
    typeof(x) p = 9;
#endif
    return x;
}
