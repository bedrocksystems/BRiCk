(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From bedrock.lang.prelude Require Import base.

Definition vaddr : Set := N.
Bind Scope N_scope with vaddr.

Definition paddr : Set := N.
Bind Scope N_scope with paddr.
