/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

enum A : int {
  X = 0,
  Y = 1,
};

enum B : unsigned char {
  XX, YY
};

void g(B) { }

void f(A x) {
  g(XX);
}

