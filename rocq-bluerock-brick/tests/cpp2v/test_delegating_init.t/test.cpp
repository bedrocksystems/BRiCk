/*
 * Copyright (C) BlueRock Security Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

struct Foo {
    Foo() {};
    Foo(int):Foo() {}
};
