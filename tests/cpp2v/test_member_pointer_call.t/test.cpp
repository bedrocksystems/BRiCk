/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

struct X {
    int y;
    int f() { return 0; }
};

template<int (X::*FUN)()>
int g() {
  X x;
  x.f();
  return (x.*FUN)(); //<-- SIGSEGV
};

int main() {
  return g<&X::f>();
}
