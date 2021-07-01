(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Import this module to make uPred mostly non-affine, while still assuming [▷ emp ⊣⊢ emp].
This is guaranteed not to affect clients, since all we add is a few [#[export] Hints].
*)

From bedrock.lang Require Import prelude.base bi.prelude bi.only_provable.
From iris.bi Require Import monpred.
From iris.proofmode Require Import tactics.

#[export] Remove Hints uPred_affine : typeclass_instances.
#[export] Remove Hints monPred_bi_affine : typeclass_instances.

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

(* Here, we assume [affinely_sep] as reasonable,
and derive desirable consequences, such as BiPositive. *)
Section with_affinely_sep.
  Context {PROP : bi} (Haffinely_sep : ∀ P Q : PROP, <affine> (P ∗ Q) ⊣⊢ <affine> P ∗ <affine> Q).
  Local Set Default Proof Using "Haffinely_sep".

  (* Iris proves [affinely_sep] from [BiPositive PROP]; we prove the converse holds *)
  (* [BiPositive PROP] is equivalent to [affinely_sep], which in turn seems
  perfectly natural. *)
  #[local] Instance bi_positive_with_affinely_sep : BiPositive PROP.
  Proof. intros P Q. by rewrite (Haffinely_sep P Q) (affinely_elim Q). Qed.
End with_affinely_sep.

(**
Specialize the lemmas in [Section with_later_emp] to [uPred] (hence
[iProp] and for now [mpred]).

All lemmas use suffix [_uPred].
*)

Section uPred_with_later_emp.
  Context (M : ucmraT).

  Definition later_emp_uPred := @bi.later_emp _ (uPred_affine M).

  (* TODO: switch to [#[export] Instance] when Coq supports it. *)
  #[local] Instance timeless_emp_uPred : Timeless (PROP := uPredI M) emp.
  Proof. apply timeless_emp_with_later_emp, later_emp_uPred. Qed.

  #[local] Instance affine_later_emp_uPred : Affine (PROP := uPredI M) (▷ emp).
  Proof. apply affine_later_emp_with_later_emp, later_emp_uPred. Qed.

  #[local] Instance affine_later_uPred (P : uPredI M) :
    Affine P → Affine (▷ P).
  Proof. apply affine_later_with_later_emp, later_emp_uPred. Qed.
End uPred_with_later_emp.

#[export] Hint Resolve timeless_emp_uPred affine_later_emp_uPred affine_later_uPred : typeclass_instances.

Section monPred_lift.
  Context (PROP : bi).
  Context (I : biIndex).
  Local Notation monPredI := (monPredI I PROP).

  (* TODO: switch to [#[export] Instance] when Coq supports it. *)
  #[local] Instance timeless_emp_monPred_lift (HT : Timeless (PROP := PROP) emp) :
    Timeless (PROP := monPredI) emp.
  Proof. constructor=> i. rewrite monPred_at_later monPred_at_except_0 monPred_at_emp. exact HT. Qed.

  #[local] Instance affine_later_emp_monPred_lift (HA : Affine (PROP := PROP) (▷ emp)) :
    Affine (PROP := monPredI) (▷ emp).
  Proof. constructor=> i. rewrite monPred_at_later monPred_at_emp. exact HA. Qed.

  #[local] Instance affine_later_monPred_lift (P : monPredI)
    (HA : ∀ P : PROP, Affine P → Affine (▷ P)) :
    Affine P → Affine (▷ P).
  Proof. intros AP. constructor=> i. rewrite monPred_at_later monPred_at_emp. apply HA, monPred_at_affine, AP. Qed.
End monPred_lift.

#[export] Hint Resolve timeless_emp_monPred_lift affine_later_emp_monPred_lift affine_later_monPred_lift : typeclass_instances.

(**
Other instances that we derive from affinity but seem safe.
*)

(*
This proves that
[ (∀ x : A, [| φ x |]) ⊢@{PROP} <affine> (∀ x : A, [| φ x |]) ]
so is related to [affinely_sep].
*)
Definition bi_emp_forall_only_provable_uPred (M : ucmraT) : BiEmpForallOnlyProvable (uPredI M) :=
  bi_affine_emp_forall_only_provable (uPred_affine M).
#[export] Hint Resolve bi_emp_forall_only_provable_uPred : typeclass_instances.

Section uPred_affinely_sep.
  Context (M : ucmraT).
  Definition affinely_sep_uPred := @affinely_sep _ (@bi_affine_positive _ (uPred_affine M)).

  #[local] Instance bi_positive_uPred : BiPositive (uPredI M).
  Proof. apply bi_positive_with_affinely_sep, affinely_sep_uPred. Qed.
End uPred_affinely_sep.

#[export] Hint Resolve bi_positive_uPred : typeclass_instances.
