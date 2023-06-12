/*
 * Copyright (c) BedRock Systems Inc. 2022
 *
 * SPDX-License-Identifier: MIT-0
 */

int printf(const char *s, ...);

void test() {
    printf("hello");
    printf(", %s", "world");
    printf("%c", '\n');
}
