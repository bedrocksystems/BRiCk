/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
extern void putstr(const char*);

int main(int argc, char* argv[])
{
    for (int i = 0; i < argc; i++) {
        putstr(argv[i]);
    }
    return 0;
}
