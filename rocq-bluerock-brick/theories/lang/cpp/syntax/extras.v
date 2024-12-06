(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.syntax.prelude.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.compare.

Definition by_tag_comparison {T} (f : T -> positive)
  : Comparison (fun a b => Pos.compare (f a) (f b)).
Proof.
  constructor; intros *; apply numbers.positive_comparison.
Qed.

#[global] Instance function_qualifiers_comparison : Comparison function_qualifiers.compare.
Proof. eapply by_tag_comparison. Qed.

#[global] Instance function_qualifiers_leibniz_cmp : LeibnizComparison function_qualifiers.compare.
Proof.
  apply by_tag_leibniz.
  compute. destruct x, y; congruence.
Qed.

#[global] Instance function_quailfiers_eq_dec : EqDecision function_qualifiers.t :=
  from_comparison.

#[global] Instance atomic_name__eq_dec {A : Set} `{!EqDecision A} : EqDecision (atomic_name_ A).
Proof. solve_decision. Defined.

#[global] Instance classname_eq_dec {lang} : EqDecision (classname' lang).
Proof. destruct lang; solve_decision. Defined.
