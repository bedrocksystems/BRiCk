/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

template<typename T>
void destroy(T* ptr) {
  ptr->T::~T();
}

template void destroy<int>(int*);
