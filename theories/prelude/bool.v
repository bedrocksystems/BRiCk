(*
 * Copyright (C) BedRock Systems Inc. 2020-21
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export bedrock.prelude.base.

#[local] Set Printing Coercions.

Lemma Is_true_is_true b : Is_true b ↔ is_true b.
Proof. by destruct b. Qed.
Lemma Is_true_eq b : Is_true b ↔ b = true.
Proof. by rewrite Is_true_is_true. Qed.

#[global] Instance orb_comm' : Comm (=) orb := orb_comm.
#[global] Instance orb_assoc' : Assoc (=) orb := orb_assoc.

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
