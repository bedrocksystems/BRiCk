/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:MIT-0
 */

enum X { Y , Z };

enum A : int { B , C };


typedef X TD;
typedef A TE;

#if 0
typedef enum { U } Unit;

typedef enum { V } unit;
#endif
