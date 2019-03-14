/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
namespace A {
  // foo_spec
  int foo(int);
  // bar_spec
  int bar(int x) {
    return foo(x) + 1;
  }
}
