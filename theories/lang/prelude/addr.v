(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.prelude Require Import base.

Definition vaddr : Set := N.
Bind Scope N_scope with vaddr.

Definition paddr : Set := N.
Bind Scope N_scope with paddr.
