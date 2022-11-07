(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(*
 * The following code contains code derived from code original to the
 * stdpp project. That original code is
 *
 *	Copyright stdpp developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original stdpp License:
 * https://gitlab.mpi-sws.org/iris/stdpp/-/blob/5415ad3003fd4b587a2189ddc2cc29c1bd9a9999/LICENSE
 *)

From bedrock.prelude Require Import base.

(**
Haskell's [Data.Function.on]
(https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Function.html#v:on).

Examples:
- Lift relation [R] by precomposing with function [f] (with [C := Prop].
  We provide theory specialized to this use-case.
*)
(* TODO: namespace, and move from [option]. This is only _used_ here.*)
Definition on {A B C} (R : B -> B -> C) (f : A -> B) (x y : A) : C :=
  R (f x) (f y).

(** Preorder properties lift through [on].
Only import locally when declaring specialized instances!
These instances can lead to divergence of setoid rewriting, so they're only
available when importing [on_props]. *)
Module on_props.
Section on_props.
  Context {A B : Type} {f : A -> B}.
  (* We use both [R] and [strict R] *)
  Implicit Type (R : relation B).

  (* We can safely make this global. *)
  #[global] Instance on_decidable `{!RelDecision R} : RelDecision (on R f).
  Proof. GUARD_TC. rewrite /on => ??. apply _. Defined.

  (** * Lift basic relation typeclasses from [RelationClasses] *)
  #[export] Instance on_reflexive `{!Reflexive R} : Reflexive (on R f).
  Proof. GUARD_TC. rewrite /on. by intros ?. Qed.
  #[export] Instance on_irreflexive `{!Irreflexive R} : Irreflexive (on R f).
  Proof. GUARD_TC. rewrite /on. by intros ??%irreflexivity. Qed.

  #[export] Instance on_symmetric `{!Symmetric R} : Symmetric (on R f).
  Proof. GUARD_TC. rewrite /on. by intros ?. Qed.
  #[export] Instance on_asymmetric `{!Asymmetric R} : Asymmetric (on R f).
  Proof. GUARD_TC. rewrite /on. intros ??. apply: asymmetry. Qed.

  #[export] Instance on_transitive `{!Transitive R} : Transitive (on R f).
  Proof. GUARD_TC. rewrite /on. by intros ???; etrans. Qed.

  (** * Lift bundled relation typeclasses from [RelationClasses] *)
  #[export] Instance on_equivalence `{!Equivalence R} : Equivalence (on R f).
  Proof. GUARD_TC. split; apply _. Qed.
  #[export] Instance on_preorder `{!PreOrder R} : PreOrder (on R f).
  Proof. GUARD_TC. split; apply _. Qed.
  #[export] Instance on_per `{!RelationClasses.PER R} : RelationClasses.PER (on R f).
  Proof. GUARD_TC. split; apply _. Qed.
  #[export] Instance on_strict_order `{!StrictOrder R} : StrictOrder (on R f).
  Proof. GUARD_TC. split; apply _. Qed.

  (** * Lift basic relation typeclasses from [stdpp.base] *)
  #[export] Instance on_antisymm
      (S : relation B) `{!AntiSymm S R} :
    AntiSymm (on S f) (on R f) | 100.
  Proof. GUARD_TC. rewrite /on. intros ??. apply: anti_symm. Qed.

  (** Needed to lift [PartialOrder] *)
  #[export] Instance on_antisymm_eq_inj
      `{!AntiSymm (=) R} `{!Inj eq eq f} :
    AntiSymm (=) (on R f).
  Proof. GUARD_TC. rewrite /on. intros ????. apply (inj f). exact: anti_symm. Qed.

  (** Needed to lift [TotalOrder] *)
  #[export] Instance on_trichotomy
      `{!Trichotomy R} `{!Inj eq eq f} :
    Trichotomy (on R f).
  Proof. GUARD_TC. rewrite /on. intros ??. rewrite -(inj_iff f). apply: trichotomy. Qed.

  #[export, refine] Instance on_trichotomyT
      `{!TrichotomyT R} `{!Inj eq eq f} :
    TrichotomyT (on R f) := fun x y =>
      match trichotomyT R (f x) (f y) with
      | inleft (left H) => inleft (left H)
      | inleft (right H) => inleft (right _)
      | inright H => inright H
      end.
  Proof. abstract (apply (inj f _ _ H)). Defined.

  (** * Lift bundled relation typeclasses from [stdpp.base] *)
  #[export] Instance on_partial_order `{!PartialOrder R} `{!Inj eq eq f} : PartialOrder (on R f).
  Proof. GUARD_TC. split; apply _. Qed.

  #[export] Instance on_total_order `{!TotalOrder R} `{!Inj eq eq f} : TotalOrder (on R f).
  Proof. GUARD_TC. split; rewrite -?[strict (on R f)]/(on (strict R) f); apply _. Qed.
End on_props.
End on_props.
#[global] Typeclasses Opaque on.

Definition some_Forall2 `(R : relation A) (oa1 oa2 : option A) :=
  is_Some oa1 ∧ is_Some oa2 ∧ option_Forall2 R oa1 oa2.

Section some_Forall2.
  Context `{R : relation A}.

  (* #[global] Instance some_Forall2_reflexive `{!Reflexive R}: Reflexive (some_Forall2 R).
  Proof. rewrite /some_Forall2. intros ?. Qed. *)
  #[global] Instance some_Forall2_symmetric `{!Symmetric R}: Symmetric (some_Forall2 R).
  Proof. GUARD_TC. rewrite /some_Forall2. intros ?; naive_solver. Qed.
  #[global] Instance some_Forall2_transitive `{!Transitive R}: Transitive (some_Forall2 R).
  Proof. GUARD_TC. rewrite /some_Forall2. intros ?; intuition idtac. by etrans. Qed.
  #[global] Instance some_Forall2_per `{!RelationClasses.PER R} : RelationClasses.PER (some_Forall2 R).
  Proof. GUARD_TC. rewrite /some_Forall2. split; apply _. Qed.

  Lemma some_Forall2_iff oa1 oa2 :
    some_Forall2 R oa1 oa2 ↔
    ∃ (a1 a2 : A), oa1 = Some a1 ∧ oa2 = Some a2 ∧ R a1 a2.
  Proof.
    unfold some_Forall2; split.
    { destruct 1 as ([??] & [??] & Hop); inversion Hop; naive_solver. }
    destruct 1 as (? & ? & -> & -> & ?); split_and!; by econstructor.
  Qed.

  #[global, refine] Instance option_Forall2_decision
      `{EqDecision A} `{!RelDecision R} :
    RelDecision (option_Forall2 R) :=
    fun oa1 oa2 =>
      match oa1, oa2 with
      | None, None => left _
      | Some a1, Some a2 => cast_if (decide (R a1 a2))
      | _, _ => right _
      end.
  Proof.
    all: abstract (intros; by [inversion_clear 1 | constructor]).
  Defined.

  #[global] Instance some_Forall2_decision `{EqDecision A} `{!RelDecision R} :
    RelDecision (some_Forall2 R).
  Proof. intros ??. apply _. Defined.
End some_Forall2.
#[global] Typeclasses Opaque some_Forall2.

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
  Import on_props.

  #[global] Instance same_property_per : RelationClasses.PER (same_property obs) := _.
  #[global] Instance: RewriteRelation (same_property obs) := {}.

  Lemma same_property_iff a1 a2 :
    same_property obs a1 a2 ↔
    ∃ (b : B), obs a1 = Some b ∧ obs a2 = Some b.
  Proof. by rewrite /same_property /on some_Forall2_eq_iff. Qed.

  Lemma same_property_intro a1 a2 b :
    obs a1 = Some b -> obs a2 = Some b -> same_property obs a1 a2.
  Proof. rewrite same_property_iff. eauto. Qed.

  Lemma same_property_reflexive_equiv a :
    is_Some (obs a) ↔ same_property obs a a.
  Proof. rewrite same_property_iff /is_Some. naive_solver. Qed.

  Lemma same_property_partial_reflexive a b :
    obs a = Some b → same_property obs a a.
  Proof. rewrite -same_property_reflexive_equiv. naive_solver. Qed.

  #[global] Instance same_property_decision `{EqDecision B} :
    RelDecision (same_property obs) := _.
End same_property.
#[global] Typeclasses Opaque same_property.

Section add_opt.
  Definition add_opt (oz1 oz2 : option Z) : option Z := liftM2 Z.add oz1 oz2.
  #[global] Instance add_opt_inj a : Inj eq eq (add_opt (Some a)).
  Proof.
    rewrite /add_opt => -[b1|] [b2|] // [?]. f_equal. lia.
  Qed.
End add_opt.
