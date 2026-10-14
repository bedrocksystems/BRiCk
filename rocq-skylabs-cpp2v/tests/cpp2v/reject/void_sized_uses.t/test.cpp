/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

unsigned long size() { return sizeof(void); }
unsigned long align() { return alignof(void); }
unsigned long gnu_align() { return __alignof__(void); }

void *add(void *p) { return p + 1; }
void *sub(void *p) { return p - 1; }
void preinc(void *p) { ++p; }
void postinc(void *p) { p++; }
void predec(void *p) { --p; }
void postdec(void *p) { p--; }
void add_assign(void *p) { p += 1; }
void sub_assign(void *p) { p -= 1; }
long diff(void *p, void *q) { return p - q; }

void deref(void *p) { (void)*p; }
void subscript(void *p) { (void)p[0]; }

void arr[2];
