(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.bi.prelude.
Require Import iris.bi.bi iris.bi.monpred.
Require Import iris.proofmode.tactics.

(** * Observations *)
(** We define type classes for making observations and a few instances
lifting those observations through the logic. Additional instances are
defined elsewhere. *)

(** [Observe Q P] means we can observe [Q] (persistently) given [P].
Such observations do not consume [P]. *)
Class Observe {PROP : bi} (Q P : PROP) := observe : P ⊢ <pers> Q.
Instance: Params (@observe) 4 := {}.
Arguments observe {_} (_ _)%I {_} : assert.
Arguments Observe {_} (_ _)%I : simpl never, assert.
Hint Mode Observe + ! ! : typeclass_instances.

(** [Observe Q P1 P2] means we can observe [Q] (persistently) given
[P1 ** P2]. Such observations do not consume the [P_i]. *)
Class Observe2 {PROP : bi} (Q P1 P2 : PROP) := observe_2 : P1 ⊢ P2 -∗ <pers> Q.
Instance: Params (@observe_2) 5 := {}.
Arguments observe_2 {_} (_ _ _)%I {_} : assert.
Arguments Observe2 {_} (_ _ _)%I : simpl never, assert.
Hint Mode Observe2 + ! ! ! : typeclass_instances.

Instance Observe_proper {PROP : bi} :
  Proper ((≡) ==> (≡) ==> (↔)) (@Observe PROP).
Proof. solve_proper. Qed.
Instance Observe2_proper {PROP : bi} :
  Proper ((≡) ==> (≡) ==> (≡) ==> (↔)) (@Observe2 PROP).
Proof. solve_proper. Qed.

(** An example of using [observe] in the IPM *)
Section example.
  Context `{PROP : bi}.
  Context (Q P : PROP) {A} (R : A → PROP) (x y : A).
  Context `{!Observe [| x = y |] P}.
  Context `{!Observe Q (R y)}.

  Goal P ⊢ R x -∗ P ∗ R y ∗ Q.
  Proof.
    iIntros "P R".
    iDestruct (observe [| x = y |] with "P") as %->.
    iDestruct (observe Q with "R") as "#$".
    iFrame "P R".
  Abort.
End example.

Section observe.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  Lemma observe_curry Q P1 P2 : Observe2 Q P1 P2 → Observe Q (P1 ∗ P2).
  Proof. intros Hobs. rewrite /Observe. apply bi.wand_elim_l', Hobs. Qed.
  Lemma observe_uncurry Q P1 P2 : Observe Q (P1 ∗ P2) → Observe2 Q P1 P2.
  Proof. intros Hobs. rewrite /Observe2. apply bi.wand_intro_r, Hobs. Qed.

  (** Alternatives for eliminating observations *)
  (** We favor declaring observations with [only_provable] over [bi_pure]. *)
  Lemma observe_elim_pure (Q : Prop) P `{!Observe [| Q |] P} : P ⊢ ⌜Q⌝.
  Proof. rewrite (observe [| _ |] P). by iIntros "#%". Qed.
  Lemma observe_elim_strong Q P `{!Observe Q P} : P ⊢ P ∗ □ Q.
  Proof.
    rewrite -{1}(idemp bi_and P) {2}(observe Q P).
    by rewrite bi.persistently_and_intuitionistically_sep_r.
  Qed.
  Lemma observe_elim Q P `{!Observe Q P} : P ⊢ P ∗ Q.
  Proof.
    by rewrite {1}(observe_elim_strong Q P) bi.intuitionistically_elim.
  Qed.

  Lemma observe_2_elim_pure (Q : Prop) P1 P2 `{!Observe2 [| Q |] P1 P2} :
    P1 ⊢ P2 -∗ ⌜Q⌝.
  Proof. rewrite (observe_2 [| _ |] P1 P2). f_equiv. by iIntros "#%". Qed.
  Lemma observe_2_elim_strong Q P1 P2 `{!Observe2 Q P1 P2} :
    P1 ⊢ P2 -∗ P1 ∗ P2 ∗ □ Q.
  Proof.
    apply bi.wand_intro_r. rewrite assoc.
    by apply observe_elim_strong, observe_curry.
  Qed.
  Lemma observe_2_elim Q P1 P2 `{!Observe2 Q P1 P2} : P1 ⊢ P2 -∗ P1 ∗ P2 ∗ Q.
  Proof.
    by rewrite {1}(observe_2_elim_strong Q P1 P2) bi.intuitionistically_elim.
  Qed.

  (** Alternatives for introducing observations *)
  Lemma observe_intro_persistent Q P `{!Persistent Q} : (P ⊢ Q) → Observe Q P.
  Proof. rewrite/Observe=>->. iIntros "#$". Qed.

  Lemma observe_intro Q P `{!Persistent Q} : (P ⊢ P ∗ Q) → Observe Q P.
  Proof. rewrite/Observe {1}(persistent Q)=>->. iIntros "[_ $]". Qed.

  Lemma observe_2_intro_persistent Q P1 P2 `{!Persistent Q} :
    (P1 ⊢ P2 -∗ Q) → Observe2 Q P1 P2.
  Proof. rewrite/Observe2=>->. f_equiv. iIntros "#$". Qed.

  Lemma observe_2_intro Q P1 P2 `{!Persistent Q} :
    (P1 ⊢ P2 -∗ P1 ∗ P2 ∗ Q) → Observe2 Q P1 P2.
  Proof.
    rewrite/Observe2 {1}(persistent Q)=>->. f_equiv. iIntros "(_ &_ & $)".
  Qed.

End observe.
Arguments observe_elim_pure {_} _%type _%I {_} : assert.
Arguments observe_elim_strong {_} (_ _)%I {_} : assert.
Arguments observe_elim {_} (_ _)%I {_} : assert.
Arguments observe_2_elim_pure {_} _%type (_ _)%I {_} : assert.
Arguments observe_2_elim_strong {_} (_ _ _)%I {_} : assert.
Arguments observe_2_elim {_} (_ _ _)%I {_} : assert.

Section proof_mode.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  (** Enable things like [iIntros] and [iDestruct] when the goal is
      [Observe Q P], as well as [iApply lem] when [lem] is an
      observation instance. *)
  Lemma test_before Q P : Observe Q P.
  Proof. Fail iIntros "P". Abort.
  Lemma test_before `{Hobs : !Observe Q P} : P ⊢ <pers> Q.
  Proof. Fail iApply Hobs. Abort.
  Global Instance observe_as_emp_valid Q P :
    AsEmpValid (Observe Q P) (P -∗ <pers> Q).
  Proof.
    rewrite/AsEmpValid/Observe. split.
    - move=>->. by auto.
    - move/bi.wand_elim_r'. by rewrite right_id.
  Qed.
  Lemma test_after `{Hobs : !Observe Q P} : P ⊢ <pers> Q.
  Proof. iApply Hobs. Abort.
  Lemma test_after Q P : Observe Q P.
  Proof. iIntros "P". Abort.

  Lemma test_before Q P1 P2 : Observe2 Q P1 P2.
  Proof. Fail iIntros "P1 P2". Abort.
  Lemma test_before `{Hobs : !Observe2 Q P1 P2} : P1 ⊢ P2 -∗ <pers> Q.
  Proof. Fail iApply Hobs. Abort.
  Global Instance observe_2_as_emp_valid Q P1 P2 :
    AsEmpValid (Observe2 Q P1 P2) (P1 -∗ P2 -∗ <pers> Q).
  Proof.
    rewrite/AsEmpValid/Observe2. split.
    - move=>->. apply bi.wand_intro_r, bi.emp_sep_2.
    - move/bi.wand_elim_r'. by rewrite right_id.
  Qed.
  Lemma test_after Q P1 P2 : Observe2 Q P1 P2.
  Proof. iIntros "P1 P2". Abort.
  Lemma test_after `{Hobs : !Observe2 Q P1 P2} : P1 ⊢ P2 -∗ <pers> Q.
  Proof. iApply Hobs. Abort.
End proof_mode.

(** Instances *)
Section bi.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  Global Instance observe_refl Q `{!Persistent Q} : Observe Q Q.
  Proof. exact: observe_intro_persistent. Qed.

  Global Instance observe_exist {A} Q (P : A → PROP) :
    (∀ x, Observe Q (P x)) → Observe Q (∃ x, P x).
  Proof.
    intros. iDestruct 1 as (x) "P". iApply (observe with "P").
  Qed.
  Global Instance observe_2_exist {A} Q (P1 P2 : A → PROP) :
    (∀ x y, Observe2 Q (P1 x) (P2 y)) → Observe2 Q (∃ x, P1 x) (∃ y, P2 y).
  Proof.
    intros. iDestruct 1 as (x) "P1". iDestruct 1 as (y) "P2".
    iApply (observe_2 with "P1 P2").
  Qed.

  Global Instance observe_sep_l Q P R : Observe Q P → Observe Q (P ∗ R).
  Proof. intros. iIntros "[P _]". iApply (observe with "P"). Qed.
  Global Instance observe_sep_r Q P R : Observe Q P → Observe Q (R ∗ P).
  Proof. intros. iIntros "[_ P]". iApply (observe with "P"). Qed.
  Global Instance observe_2_sep_l Q P1 P2 R1 R2 :
    Observe2 Q P1 P2 → Observe2 Q (P1 ∗ R1) (P2 ∗ R2).
  Proof.
    intros. iIntros "[P1 _] [P2 _]". iApply (observe_2 with "P1 P2").
  Qed.
  Global Instance observe_2_sep_r Q P1 P2 R1 R2 :
    Observe2 Q P1 P2 → Observe2 Q (R1 ∗ P1) (R2 ∗ P2).
  Proof.
    intros. iIntros "[_ P1] [_ P2]". iApply (observe_2 with "P1 P2").
  Qed.

  Global Instance observe_or Q P R :
    Observe Q P → Observe Q R → Observe Q (P ∨ R).
  Proof.
    intros. iIntros "[P|R]".
    by iApply (observe with "P"). by iApply (observe with "R").
  Qed.
  Global Instance observe_2_or Q P1 P2 R1 R2 :
    Observe2 Q P1 P2 → Observe2 Q P1 R2 →
    Observe2 Q R1 P2 → Observe2 Q R1 R2 →
    Observe2 Q (P1 ∨ R1) (P2 ∨ R2).
  Proof.
    intros. iIntros "[P1|R1] [P2|R2]".
    - iApply (observe_2 with "P1 P2").
    - iApply (observe_2 with "P1 R2").
    - iApply (observe_2 with "R1 P2").
    - iApply (observe_2 with "R1 R2").
  Qed.
End bi.

Section monpred.
  Context {I : biIndex} {PROP : bi}.
  Implicit Types i : I.
  Implicit Types P Q : (monPred I PROP).

  (** It's not clear these should be instances. *)
  Lemma monPred_observe Q P :
    (∀ i, Observe (Q i) (P i)) → Observe Q P.
  Proof.
    rewrite/Observe=>Hobs. constructor=>i.
    by rewrite (Hobs i) monPred_at_persistently.
  Qed.
  Lemma monPred_observe_2 Q P1 P2 :
    (∀ i, Observe2 (Q i) (P1 i) (P2 i)) → Observe2 Q P1 P2.
  Proof.
    intros Hobs. apply observe_uncurry, monPred_observe=>i.
    rewrite monPred_at_sep. by apply observe_curry.
  Qed.

  (** These should certainly not be instances. *)
  Lemma observe_monPred_at Q P i : Observe Q P → Observe (Q i) (P i).
  Proof.
    intros [Hobs]. rewrite/Observe (Hobs i).
    by rewrite monPred_at_persistently.
  Qed.
  Lemma observe_2_monPred_at Q P1 P2 i :
    Observe2 Q P1 P2 → Observe2 (Q i) (P1 i) (P2 i).
  Proof.
    intros [Hobs]. rewrite/Observe2 (Hobs i).
    by rewrite monPred_wand_force monPred_at_persistently.
  Qed.

  Global Instance observe_pure_monPred_at (Q : Prop) P i :
    Observe [! Q !] P → Observe [! Q !] (P i).
  Proof.
    intros. rewrite -(monPred_at_pure i). by apply observe_monPred_at.
  Qed.
  Global Instance observe_2_pure_monPred (Q : Prop) P1 P2 i :
    Observe2 [! Q !] P1 P2 → Observe2 [! Q !] (P1 i) (P2 i).
  Proof.
    intros. rewrite -(monPred_at_pure i). by apply observe_2_monPred_at.
  Qed.

  Global Instance observe_only_provable_monPred_at (Q : Prop) P i :
    Observe [| Q |] P → Observe [| Q |] (P i).
  Proof.
    intros. rewrite -(monPred_at_only_provable i). by apply observe_monPred_at.
  Qed.
  Global Instance observe_2_only_provable_monPred_at (Q : Prop) P1 P2 i :
    Observe2 [| Q |] P1 P2 → Observe2 [| Q |] (P1 i) (P2 i).
  Proof.
    intros. rewrite -(monPred_at_only_provable i).
    by apply observe_2_monPred_at.
  Qed.
End monpred.

Section embed.
  Context `{BiEmbed PROP1 PROP2}.
  Local Notation embed := (embed (A:=PROP1) (B:=PROP2)).
  Implicit Types P Q : PROP1.

  Global Instance embed_observe Q P : Observe Q P → Observe (embed Q) (embed P).
  Proof.
    rewrite/Observe=>->. by rewrite embed_persistently.
  Qed.
  Global Instance embed_observe_2 Q P1 P2 :
    Observe2 Q P1 P2 → Observe2 (embed Q) (embed P1) (embed P2).
  Proof.
    intros Hobs. apply observe_uncurry. rewrite -embed_sep.
    by apply embed_observe, observe_curry.
  Qed.
End embed.
