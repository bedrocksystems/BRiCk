/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

struct Foo {
  int a { 1 };
  int b = 2;

  Foo() {}
  Foo(int x) : b(x) {}
};
