/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

template<typename T, int res>
int g(T x) {
    return res;
}

int main() {
    g<int, 8>(1);
}
