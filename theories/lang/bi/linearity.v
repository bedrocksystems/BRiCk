(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Import this module to make uPred mostly non-affine, while still assuming [▷ emp
⊣⊢ emp] and other principles that do not cause leaks.

All changes to [typeclass_instances] will not propagate to your clients:
technically, they have [#[export]] visibility.
*)

Require Import bedrock.prelude.base.
From bedrock.lang Require Import bi.prelude bi.only_provable.
From iris.bi Require Import monpred.
From iris.proofmode Require Import proofmode.
From iris.bi Require Import laterable.

(* Disable [BiAffine uPred] *)
#[export] Remove Hints uPred_affine : typeclass_instances.

(*
As a small optimization, we can remove dependent instances.
This causes further incompleteness if other affine logics are relevant.
*)
#[export] Remove Hints monPred_bi_affine : typeclass_instances.
#[export] Remove Hints absorbing_bi : typeclass_instances.
#[export] Remove Hints persistent_laterable : typeclass_instances.

(* Potentially useful to exploit [siProp_affine]. *)
Module enable_absorbing_bi.
  #[export] Hint Resolve absorbing_bi : typeclass_instances.
End enable_absorbing_bi.

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

  #[local] Lemma persistent_affine_laterable (P : PROP) :
    Persistent P → Affine P → Laterable P.
  Proof. intros. apply /intuitionistic_laterable /timeless_emp_with_later_emp. Qed.
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
  Context (M : ucmra).
  Implicit Type (P : uPredI M).

  Definition later_emp_uPred := @bi.later_emp _ (uPred_affine M).

  (* TODO: switch to [#[export] Instance] when Coq supports it. *)
  #[local] Instance timeless_emp_uPred : Timeless (PROP := uPredI M) emp.
  Proof. apply timeless_emp_with_later_emp, later_emp_uPred. Qed.

  #[local] Instance affine_later_emp_uPred : Affine (PROP := uPredI M) (▷ emp).
  Proof. apply affine_later_emp_with_later_emp, later_emp_uPred. Qed.

  #[local] Instance affine_later_uPred P :
    Affine P → Affine (▷ P).
  Proof. apply affine_later_with_later_emp, later_emp_uPred. Qed.

  #[local] Instance persistent_affine_laterable_upred P :
    Persistent P → Affine P → Laterable P.
  Proof. apply persistent_affine_laterable, later_emp_uPred. Qed.
End uPred_with_later_emp.

#[export] Hint Resolve timeless_emp_uPred affine_later_emp_uPred
  affine_later_uPred persistent_affine_laterable_upred : typeclass_instances.

(** *** Other instances that we derive from affinity but seem safe. *)
Section uPred.
  Context (M : ucmra).
  Definition affinely_sep_uPred := @affinely_sep _ (@bi_affine_positive _ (uPred_affine M)).

  #[local] Instance bi_positive_uPred : BiPositive (uPredI M).
  Proof. apply bi_positive_with_affinely_sep, affinely_sep_uPred. Qed.

  (*
  This instance is needed by some [only_provable] lemmas. It proves that
  [ (∀ x : A, [| φ x |]) ⊢@{PROP} <affine> (∀ x : A, [| φ x |]) ]
  so it seems related to [affinely_sep].
  *)
  #[local] Instance bi_emp_forall_only_provable_uPred (M : ucmra) : BiEmpForallOnlyProvable (uPredI M) :=
    bi_affine_emp_forall_only_provable (uPred_affine M).
End uPred.

#[export] Hint Resolve bi_positive_uPred bi_emp_forall_only_provable_uPred : typeclass_instances.

(** *** Lift over [monPred] instances declared above. *)
Section monPred_lift.
  Context (PROP : bi).
  Context (I : biIndex).
  Local Notation monPredI := (monPredI I PROP).
  Implicit Type (P : monPredI).

  (* TODO: switch to [#[export] Instance] when Coq supports it. *)
  #[local] Instance timeless_emp_monPred_lift (HT : Timeless (PROP := PROP) emp) :
    Timeless (PROP := monPredI) emp.
  Proof. constructor=> i. rewrite monPred_at_later monPred_at_except_0 monPred_at_emp. exact HT. Qed.

  #[local] Instance affine_later_emp_monPred_lift (HA : Affine (PROP := PROP) (▷ emp)) :
    Affine (PROP := monPredI) (▷ emp).
  Proof. constructor=> i. rewrite monPred_at_later monPred_at_emp. exact HA. Qed.

  #[local] Instance affine_later_monPred_lift P
    (HA : ∀ P : PROP, Affine P → Affine (▷ P)) :
    Affine P → Affine (▷ P).
  Proof.
    intros AP. constructor=> i. rewrite monPred_at_later monPred_at_emp.
    apply HA, monPred_at_affine, AP.
  Qed.

  #[local] Instance persistent_affine_laterable_monPred_lift P
    (HT : Timeless (PROP := PROP) emp) :
    Persistent P → Affine P → Laterable P.
  Proof. intros. apply: intuitionistic_laterable. Qed.
  (** Liftings for [BiPositive] and [BiEmpForallOnlyProvable] are declared elsewhere. *)
End monPred_lift.

#[export] Hint Resolve timeless_emp_monPred_lift affine_later_emp_monPred_lift
affine_later_monPred_lift persistent_affine_laterable_monPred_lift : typeclass_instances.
