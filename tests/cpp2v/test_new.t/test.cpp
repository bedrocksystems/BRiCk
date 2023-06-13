/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */
//#include <stdio.h>

struct C {
  ~C() { /* printf("1"); */ }
};

int main() {
  auto p = new C[5][6];
  delete[] &(p[0][0]);
}
