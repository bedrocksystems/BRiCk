/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

struct Top {
     int p;
};

struct Other {
    int x;
};

struct Foo : public Top {
    int z;
};

struct Bar : public Foo , public Other {
    int y;
};


int get_x(Bar& b) {
    return b.p + b.y;
}
