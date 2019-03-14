/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:MIT-0
 */
namespace A {
  // foo_spec
  int foo(int);
  // bar_spec
  int bar(int x) {
    return foo(x) + 1;
  }
}
