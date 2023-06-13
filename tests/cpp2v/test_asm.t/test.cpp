/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

void foo() {
    int x = 0;
    __asm__ volatile ("syscall" : "+D"(x) :: "rcx", "r11", "memory");
}
