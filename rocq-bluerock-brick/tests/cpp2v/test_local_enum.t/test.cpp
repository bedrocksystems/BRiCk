/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

void test() {
    enum X { A , B };
    struct Y { int x; X tg; };

    X a;
    Y b;

    b.x++;
    a = B;
}
