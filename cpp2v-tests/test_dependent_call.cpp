/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

template <typename T>
class X
{
  int lookup();
};

template <typename T>
int X<T>::lookup()
{
  return T::f();
}

struct Y {
    static int f() { return 0; }
};

template class X<Y>;
