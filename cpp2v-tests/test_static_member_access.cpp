/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
struct C {
  int mem;
  static int sta;
  static int get() { return 0; }
  int gett() { return 0; }
};

void test() {
  C c;
  (void)c.mem;
  (void)c.sta;
  c.get();
  c.gett();
}
