(*
 * Copyright (C) BedRock Systems Inc. 2020-2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export bedrock.prelude.base.

#[local] Set Printing Coercions.

Infix "<=" := Bool.le : bool_scope.
Notation "(<=)" := Bool.le (only parsing) : bool_scope.

(**
More flexible version of [reflect]: using [H : reflectPQ (m < n) (n ≤ m) b]
instead of [H : reflect (m < n) b] avoids introducing [~(m < n)] in the context.

Typical users will still pick [P] and [Q] such that [Q ↔ ¬P], even if that's not
strictly enforced.
*)
Variant reflectPQ (P Q : Prop) : bool -> Prop :=
| rPQ_true  (_ : P) : reflectPQ P Q true
| rPQ_false (_ : Q) : reflectPQ P Q false.

Lemma Is_true_is_true b : Is_true b ↔ is_true b.
Proof. by destruct b. Qed.
Lemma Is_true_eq b : Is_true b ↔ b = true.
Proof. by rewrite Is_true_is_true. Qed.

#[global] Instance orb_comm' : Comm (=) orb := orb_comm.
#[global] Instance orb_assoc' : Assoc (=) orb := orb_assoc.
#[global] Instance andb_comm' : Comm (=) andb := andb_comm.
#[global] Instance andb_assoc' : Assoc (=) andb := andb_assoc.

Section implb.
  Implicit Types a b : bool.

  Lemma implb_True a b : implb a b ↔ (a → b).
  Proof. by rewrite !Is_true_is_true /is_true implb_true_iff. Qed.
  Lemma implb_prop_intro a b : (a → b) → implb a b.
  Proof. by rewrite implb_True. Qed.
  Lemma implb_prop_elim a b : implb a b → a → b.
  Proof. by rewrite implb_True. Qed.
End implb.

Lemma bool_decide_Is_true (b : bool) : bool_decide (Is_true b) = b.
Proof. by case: b. Qed.

Lemma bool_decide_bool_eq b : bool_decide (b = true) = b.
Proof. by case: b. Qed.

Lemma bool_decide_is_true b : bool_decide (is_true b) = b.
Proof. by case: b. Qed.

#[global] Instance andb_left_id : LeftId (=) true andb := andb_true_l.
#[global] Instance andb_right_id : RightId (=) true andb := andb_true_r.
#[global] Instance andb_left_absorb : LeftAbsorb (=) false andb := andb_false_l.
#[global] Instance andb_right_absorb : RightAbsorb (=) false andb := andb_false_r.

#[global] Instance orb_left_id : LeftId (=) false orb := orb_false_l.
#[global] Instance orb_right_id : RightId (=) false orb := orb_false_r.
#[global] Instance orb_left_absorb : LeftAbsorb (=) true orb := orb_true_l.
#[global] Instance orb_right_absorb : RightAbsorb (=) true orb := orb_true_r.

#[global] Instance set_unfold_negb (b : bool) P :
  SetUnfold b P → SetUnfold (negb b) (¬ P).
Proof. constructor. rewrite negb_True. set_solver. Qed.

#[global] Instance set_unfold_andb (b1 b2 : bool) P Q :
  SetUnfold b1 P → SetUnfold b2 Q →
  SetUnfold (b1 && b2) (P ∧ Q).
Proof. constructor. rewrite andb_True. set_solver. Qed.

#[global] Instance set_unfold_orb (b1 b2 : bool) P Q :
  SetUnfold b1 P → SetUnfold b2 Q →
  SetUnfold (b1 || b2) (P ∨ Q).
Proof. constructor. rewrite orb_True. set_solver. Qed.

#[global] Instance set_unfold_bool_decide (P Q : Prop) `{!Decision P} :
  SetUnfold P Q → SetUnfold (bool_decide P) Q.
Proof. constructor. rewrite bool_decide_spec. set_solver. Qed.

(** Simple extensions to Coq's [Bool] *)
Module Bool.
  Export Coq.Bool.Bool.
  #[local] Open Scope bool_scope.

  (** Properties of [Bool.le] *)

  Definition leb (b1 b2 : bool) : bool :=
    if b1 then b2 else true.

  Lemma le_leb b1 b2 : b1 <= b2 <-> leb b1 b2.
  Proof. by destruct b1, b2. Qed.

  #[global] Instance le_dec : RelDecision (<=).
  Proof.
    refine (fun b1 b2 => cast_if (decide (leb b1 b2)));
      by rewrite le_leb.
  Qed.

  #[global] Instance le_pi a b : ProofIrrel (a <= b).
  Proof. destruct a, b; apply _. Qed.

  #[global] Instance le_preorder : PreOrder (<=).
  Proof. split. by intros []. by intros [] [] []. Qed.

  Lemma le_andb_l a b : a && b <= a.
  Proof. by destruct a, b. Qed.
  #[global] Hint Resolve le_andb_l : core.

  Lemma le_andb_r a b : a && b <= b.
  Proof. by destruct a, b. Qed.
  #[global] Hint Resolve le_andb_r : core.

  Lemma andb_min_l a b : a <= b -> a && b = a.
  Proof. by destruct a, b. Qed.
  Lemma andb_min_r a b : a <= b -> b && a = a.
  Proof. by destruct a, b. Qed.
End Bool.
