/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

void take(void *);

bool f(int *q, void *p, void *r) {
  void *v = q;
  take(p);
  take(static_cast<void *>(q));
  int *back = static_cast<int *>(v);
  (void)back;
  return p == r && p != nullptr && p < r;
}
