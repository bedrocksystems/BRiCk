(*
 * Copyright (c) 2020-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import locker.
From bedrock.lang Require Import bi.prelude.

(* points-to *)
Structure AT : Type :=
  { #[canonical=yes] AT_LHS : Type
  ; #[canonical=no] AT_RHS : Type
  ; #[canonical=yes] AT_Result : Type
  ; #[canonical=no] AT_at : AT_LHS -> AT_RHS -> AT_Result }.
#[global] Arguments AT_at {AT} _ _ : rename, simpl never.
#[global] Bind Scope bi_scope with AT_RHS.

mlock Definition __at := @AT_at.
#[global] Arguments __at {AT} _ _ : rename.

#[global] Notation "p |-> r" := (__at p r)
  (at level 15, r at level 20, right associativity) : stdpp_scope.
