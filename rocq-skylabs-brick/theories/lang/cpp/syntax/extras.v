(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.compare.
Require Import skylabs.lang.cpp.syntax.prelude.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.compare.

#[global] Instance function_qualifiers_comparison : Comparison function_qualifiers.compare.
Proof. apply by_prim_tag_comparison. Qed.

#[global] Instance: Inj eq eq core.function_qualifiers.tag_prim.
Proof. by intros [] []. Qed.

#[global] Instance function_qualifiers_leibniz_cmp : LeibnizComparison function_qualifiers.compare.
Proof. exact: by_prim_tag_leibniz. Qed.

#[global] Instance function_quailfiers_eq_dec : EqDecision function_qualifiers.t :=
  LeibnizComparison.from_comparison.

#[global] Instance atomic_name_eq_dec : EqDecision atomic_name :=
  LeibnizComparison.from_comparison.
