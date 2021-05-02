(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Import this module to make uPred mostly non-affine, while still assuming [▷ emp ⊣⊢ emp].
This is guaranteed not to affect clients, since all we add is a few [#[export] Hints].
*)

From bedrock.lang Require Import prelude.base bi.prelude.
From iris.proofmode Require Import tactics.

#[export] Remove Hints uPred_affine : typeclass_instances.

Import bi.

Section with_later_emp.
  Context {PROP : bi} (Hlater_emp : ▷ emp ⊣⊢@{PROP} emp).
  Local Set Default Proof Using "Hlater_emp".
  Local Notation "'emp'" := (bi_emp (PROP := PROP)) : bi_scope.

  (**
  Very explicit proofs of some desirable principles, for any [bi]
  supporting [Hlater_emp].

  All lemmas use suffix [_with_later_emp].
  *)

  #[local] Lemma timeless_emp_with_later_emp : Timeless emp.
  Proof. by rewrite /Timeless -except_0_intro Hlater_emp. Qed.

  #[local] Instance affine_later_emp_with_later_emp : Affine (▷ emp).
  Proof. by rewrite /Affine Hlater_emp. Qed.

  #[local] Lemma affine_later_with_later_emp {P : PROP} `{!Affine P} :
    Affine (▷ P).
  Proof. intros. by rewrite /Affine (affine P) (affine (▷ emp)). Qed.
End with_later_emp.

(**
Specialize the lemmas in [Section with_later_emp] to [uPred] (hence
[iProp] and for now [mpred]).

All lemmas use suffix [_uPred].
*)

Section uPred.
  Context (M : ucmraT).
  Local Notation "'emp'" := (bi_emp (PROP := uPredI M)) : bi_scope.

  Definition later_emp_uPred := @bi.later_emp _ (uPred_affine M).

  (* TODO: switch to [#[export] Instance] when Coq supports it. *)
  #[local] Instance timeless_emp_uPred : Timeless (PROP := uPredI M) emp.
  Proof. apply timeless_emp_with_later_emp, later_emp_uPred. Qed.

  #[local] Instance affine_later_emp_uPred : Affine (PROP := uPredI M) (▷ emp).
  Proof. apply affine_later_emp_with_later_emp, later_emp_uPred. Qed.

  #[local] Instance affine_later_uPred (P : uPredI M) :
    Affine P → Affine (▷ P).
  Proof. apply affine_later_with_later_emp, later_emp_uPred. Qed.
End uPred.

#[export] Hint Resolve timeless_emp_uPred affine_later_emp_uPred affine_later_uPred : typeclass_instances.
