(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha et al.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From bedrock.lang.prelude Require Import base.

Definition on {A B C} (R : B -> B -> C) (f : A -> B) (x y : A) : C :=
  R (f x) (f y).
Section on_props.
  Context `{R : relation B} `{f : A -> B}.

  Global Instance on_reflexive `{!Reflexive R}: Reflexive (on R f).
  Proof. rewrite /on. by intros ?. Qed.
  Global Instance on_symmetric `{!Symmetric R}: Symmetric (on R f).
  Proof. rewrite /on. by intros ?. Qed.
  Global Instance on_transitive `{!Transitive R}: Transitive (on R f).
  Proof. rewrite /on. by intros ???; etrans. Qed.
End on_props.

Definition some_Forall2 `(R : relation A) (oa1 oa2 : option A) :=
  option_Forall2 R oa1 oa2 ∧ is_Some oa1 ∧ is_Some oa2.

Section some_Forall2.
  Context `{R : relation A}.

  (* Global Instance some_Forall2_reflexive `{!Reflexive R}: Reflexive (some_Forall2 R).
  Proof. rewrite /some_Forall2. intros ?. Qed. *)
  Global Instance some_Forall2_symmetric `{!Symmetric R}: Symmetric (some_Forall2 R).
  Proof. rewrite /some_Forall2. intros ?; naive_solver. Qed.
  Global Instance some_Forall2_transitive `{!Transitive R}: Transitive (some_Forall2 R).
  Proof. rewrite /some_Forall2. intros ?; intuition idtac. by etrans. Qed.

  Lemma some_Forall2_iff oa1 oa2 :
    some_Forall2 R oa1 oa2 ↔
    ∃ (a1 a2 : A), oa1 = Some a1 ∧ oa2 = Some a2 ∧ R a1 a2.
  Proof.
    unfold some_Forall2; split.
    { destruct 1 as (Hop & [??] & [??]); inversion Hop; naive_solver. }
    destruct 1 as (? & ? & -> & -> & ?); split_and!; by econstructor.
  Qed.
End some_Forall2.

Section some_Forall2_eq.
  Context {A : Type}.

  Lemma some_Forall2_eq_iff (oa1 oa2 : option A) :
    some_Forall2 eq oa1 oa2 ↔
    ∃ (a : A), oa1 = Some a ∧ oa2 = Some a.
  Proof. rewrite some_Forall2_iff; naive_solver. Qed.
End some_Forall2_eq.

(** ** Define a partial equivalence relation from an observation *)
Definition same_property `(obs : A → option B) :=
  on (some_Forall2 eq) obs.
Section same_property.
  Context `{obs : A → option B}.

  Global Instance same_property_per : RelationClasses.PER (same_property obs).
  Proof. rewrite /same_property. split; apply _. Qed.
  Global Instance: RewriteRelation (same_property obs) := {}.

  Lemma same_property_iff a1 a2 :
    same_property obs a1 a2 ↔
    ∃ (b : B), obs a1 = Some b ∧ obs a2 = Some b.
  Proof. by rewrite /same_property /on some_Forall2_eq_iff. Qed.

  Lemma same_property_reflexive_equiv a :
    (∃ b, obs a = Some b) ↔ same_property obs a a.
  Proof. rewrite same_property_iff. naive_solver. Qed.

  Lemma same_property_partial_reflexive a b :
    obs a = Some b → same_property obs a a.
  Proof. rewrite -same_property_reflexive_equiv. naive_solver. Qed.

  Global Instance same_property_decision `{EqDecision B} :
    RelDecision (same_property obs).
  Proof.
    rewrite /RelDecision => a1 a2.
    suff: Decision (∃ (b : B), obs a1 = Some b ∧ obs a2 = Some b);
      rewrite /Decision. { case => /same_property_iff; eauto. }

    destruct (obs a1) as [b1|], (obs a2) as [b2|];
      try destruct_decide (decide (b1 = b2)) as H; subst; eauto;
      by right; naive_solver.
  Qed.
End same_property.
