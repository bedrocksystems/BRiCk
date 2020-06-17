(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.bi Require Import bi notation monpred embedding.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Global Notation lentails := (bi_entails) (only parsing).
Global Notation lequiv := (≡) (only parsing).
Global Notation ltrue := (bi_pure True) (only parsing).
Global Notation lfalse := (bi_pure False) (only parsing).
Global Notation land := (bi_and) (only parsing).
Global Notation lor := (bi_or) (only parsing).
Global Notation limpl := (bi_impl) (only parsing).
Global Notation lforall := (bi_forall) (only parsing).
Global Notation lexists := (bi_exist) (only parsing).

Global Notation empSP := (bi_emp) (only parsing).
Global Notation sepSP := (bi_sep) (only parsing).
Global Notation wandSP := (bi_wand) (only parsing).
Global Notation illater := (sbi_later) (only parsing).

Global Notation embed := (bi_pure) (only parsing).
Ltac split' := intros; apply (anti_symm (⊢)).

Definition only_provable {PROP : bi} (P : Prop) : PROP := (<affine> ⌜P⌝)%I.
Arguments only_provable {_} _%type_scope : simpl never, rename.
Instance: Params (@only_provable) 1 := {}.

(* Charge notation levels *)
Module ChargeNotation.

  Notation "P |-- Q"  := (P%I ⊢ Q%I) (at level 80, no associativity).
  Notation "P '|-@{' PROP } Q" := (P%I ⊢@{PROP} Q%I)
    (at level 80, no associativity, only parsing).

  Notation "P //\\ Q"   := (P ∧ Q)%I (at level 75, right associativity).
  Notation "P \\// Q"   := (P ∨ Q)%I (at level 76, right associativity).
  Notation "P -->> Q"   := (P → Q)%I (at level 77, right associativity).
  Notation "'Forall' x .. y , p" :=
    (lforall (fun x => .. (lforall (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).

  Notation "'Exists' x .. y , p" :=
    (lexists (fun x => .. (lexists (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).

  Notation "|--  P" := (⊢ P%I) (at level 85, no associativity).
  Notation "'|-@{' PROP } P" := (⊢@{PROP} P%I)
    (at level 85, no associativity, only parsing).

  Notation "P ** Q" := (P ∗ Q)%I (at level 58, right associativity).
  Notation "P -* Q" := (P -∗ Q)%I (at level 60, right associativity).
  Notation "'sepSPs' ps" := ([∗] ps)%I (at level 20).

  (* Notation "'|>' P" := (▷  P)%I (at level 71). *)
  Notation "|> P" := (▷  P)%I (at level 20, right associativity).

  Notation "P -|- Q"  := (P%I ≡ Q%I) (at level 85, no associativity).
  Notation "P '-|-@{' PROP } Q"  := (P%I ⊣⊢@{PROP} Q%I)
    (at level 85, no associativity, only parsing).

  Notation "'[|'  P  '|]'" := (only_provable P).

End ChargeNotation.

(* IPM notation levels *)
Module IPMNotation.
  Notation "P |-- Q" := (P ⊢ Q)%I (at level 99, Q at level 200, right associativity).
  Notation "P //\\ Q" := (P ∧ Q)%I (at level 99, Q at level 80, right associativity).
  Notation "P \\// Q" := (P ∨ Q)%I (at level 99, Q at level 85, right associativity).
  Notation "P -->> Q" := (P → Q)%I (at level 99, Q at level 200, right associativity).

  Notation "'Forall' x .. y , p" :=
    (lforall (fun x => .. (lforall (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).
  Notation "'Exists' x .. y , p" :=
    (lexists (fun x => .. (lexists (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).

  Infix "-|-"  := (⊣⊢)%I (at level 95, no associativity).
  Notation "|--  P" := (True |-- P)%I (at level 85, no associativity).

  Notation "P ** Q" := (P ∗ Q)%I (at level 80, right associativity).
  Notation "P -* Q" := (P -∗ Q)%I (at level 99, Q at level 200, right associativity,
                                   format "'[' P  '/' -*  Q ']'").
  Notation "[| P |]" := (⌜ P ⌝%I) (at level 1, P at level 200).
  Notation "[|| P ||]" := (⎡ P ⎤%I) (at level 1, P at level 200).
  Notation "'sepSPs' ps" := ([∗] ps)%I (at level 20).

  Notation "|> P" := (▷  P)%I (at level 20, right associativity).
End IPMNotation.

(** * Properties of [only_provable]. *)
Section with_notation.
Import ChargeNotation.

Section bi.
  Context {PROP : bi}.

  Global Instance only_provable_ne n :
    Proper (iff ==> dist n) (@only_provable PROP).
  Proof. solve_proper. Qed.
  Global Instance only_provable_proper :
    Proper (iff ==> (⊣⊢)) (@only_provable PROP).
  Proof. solve_proper. Qed.
  Global Instance only_provable_mono' :
    Proper (impl ==> (⊢)) (@only_provable PROP).
  Proof. solve_proper. Qed.
  Global Instance only_provable_flip_mono :
    Proper (flip impl ==> flip (⊢)) (@only_provable PROP).
  Proof. solve_proper. Qed.

  Global Instance only_provable_persistent P : Persistent (PROP:=PROP) [| P |].
  Proof. apply _. Qed.
  Global Instance only_provable_affine P : Affine (PROP:=PROP) [| P |].
  Proof. apply _. Qed.
  Global Instance only_provable_absorbing `{BiAffine PROP} P :
    Absorbing (PROP:=PROP) [| P |].
  Proof. apply _. Qed.

  Implicit Types P Q : Prop.
  Implicit Types p q r : PROP.
  Local Notation "p ⊢ q" := (p ⊢@{PROP} q) (only parsing).
  Local Notation "p ⊣⊢ q" := (p ⊣⊢@{PROP} q) (only parsing).

  Lemma only_provable_mono P Q : (P → Q) → [| P |] ⊢ [| Q |].
  Proof. apply only_provable_mono'. Qed.
  Lemma only_provable_iff P Q : (P ↔ Q) → [| P |] ⊣⊢ [| Q |].
  Proof. apply only_provable_proper. Qed.
  Lemma only_provable_intro P p `{!Affine p} : P → p ⊢ [| P |].
  Proof. intros ?. apply: bi.affinely_intro. exact: bi.pure_intro. Qed.
  Lemma only_provable_elim' P p : (P → True ⊢ p) → [| P |] ⊢ p.
  Proof. rewrite/only_provable bi.affinely_elim. exact: bi.pure_elim'. Qed.
  Lemma only_provable_elim_l P q r : (P → q ⊢ r) → [| P |] ∧ q ⊢ r.
  Proof. rewrite /only_provable bi.affinely_elim. apply bi.pure_elim_l. Qed.
  Lemma only_provable_elim_r P q r : (P → q ⊢ r) → q ∧ [| P |] ⊢ r.
  Proof. rewrite comm. apply only_provable_elim_l. Qed.
  Lemma only_provable_emp : [| True |] ⊣⊢ emp.
  Proof. by rewrite/only_provable bi.affinely_True_emp bi.affinely_emp. Qed.
  Lemma only_provable_True P : P → [| P |] ⊣⊢ emp.
  Proof. intros. by rewrite -only_provable_emp /only_provable bi.pure_True. Qed.
  Lemma only_provable_False P : ¬P → [| P |] ⊣⊢ False.
  Proof.
    intros. by rewrite /only_provable bi.pure_False// bi.affinely_False.
  Qed.
  Lemma only_provable_sep P Q : [|P ∧ Q|] ⊣⊢ [| P |] ** [| Q |].
  Proof. apply (anti_symm _); auto. Qed.
  Lemma only_provable_and P Q : [|P ∧ Q|] ⊣⊢ [| P |] ∧ [| Q |].
  Proof. by rewrite -bi.affinely_and -bi.pure_and. Qed.
  Lemma only_provable_or P Q : [|P ∨ Q|] ⊣⊢ [| P |] ∨ [| Q |].
  Proof. by rewrite -bi.affinely_or -bi.pure_or. Qed.
  Lemma only_provable_impl P Q : [|P → Q|] ⊢ ([| P |] → [| Q |]).
  Proof. auto. Qed.
  Lemma only_provable_forall {A} (φ : A → Prop) : [|∀ x, φ x|] ⊢ ∀ x, [|φ x|].
  Proof. auto. Qed.
  Lemma only_provable_exist {A} (φ : A → Prop) : [|∃ x, φ x|] ⊣⊢ ∃ x, [|φ x|].
  Proof. rewrite/only_provable. by rewrite bi.pure_exist bi.affinely_exist. Qed.
  Lemma only_provable_impl_forall P q : ([| P |] → q) ⊢ (∀ _ : P, emp → q).
  Proof. apply bi.forall_intro=>?. by rewrite only_provable_True. Qed.
  Lemma only_provable_alt P : [| P |] ⊣⊢ ∃ _ : P, emp.
  Proof.
    rewrite /only_provable bi.pure_alt bi.affinely_exist.
    do 2!f_equiv. exact: only_provable_emp.
  Qed.
  Lemma only_provable_wand_forall_1 P q : ([| P |] -∗ q) ⊢ (∀ _ : P, q).
  Proof.
    apply bi.forall_intro=>?. by rewrite only_provable_True// left_id.
  Qed.
  Lemma only_provable_wand_forall_2 P q `{!Absorbing q} :
    (∀ _ : P, q) ⊢ ([| P |] -∗ q).
  Proof. by rewrite /only_provable -bi.pure_wand_forall// bi.affinely_elim. Qed.
  Lemma only_provable_wand_forall P q `{!Absorbing q} :
    ([| P |] -∗ q) ⊣⊢ (∀ _ : P, q).
  Proof.
    apply (anti_symm _);
    auto using only_provable_wand_forall_1, only_provable_wand_forall_2.
  Qed.
End bi.
Hint Resolve only_provable_intro : core.

Section sbi.
  Context {PROP : sbi}.

  Global Instance only_provable_timeless `{BiAffine PROP} P :
    Timeless (PROP:=PROP) [| P |].
  Proof. apply _. Qed.
  Global Instance only_provable_plain `{BiPlainly PROP} P :
    Plain (PROP:=PROP) [| P |].
  Proof. apply _. Qed.
End sbi.

Section monpred.
  Context {I : biIndex} {PROP : bi}.

  Global Instance only_provable_objective P : @Objective I PROP [| P |].
  Proof. rewrite/only_provable. apply _. Qed.

  Lemma monPred_at_only_provable (i : I) P :
    monPred_at [| P |] i ⊣⊢@{PROP} [| P |].
  Proof. by rewrite monPred_at_affinely monPred_at_pure. Qed.
End monpred.

Lemma embed_only_provable `{BiEmbedEmp PROP1 PROP2} (P : Prop) :
  embedding.embed [| P |] ⊣⊢@{PROP2} [| P |].
Proof. by rewrite embed_affinely embed_pure. Qed.

Section proofmode.
  Context {PROP : bi}.

  (**
   * We don't register instances
   *
   * - [@FromAffinely PROP [| P |] ⌜P⌝]
   *
   * - [@IntoAbsorbingly PROP ⌜P⌝ [| P |]]
   *
   * as they would interact proorly with, e.g., [iSplit], changing
   * goals like [[| P |] ** Q] into subgoals involving [bi_pure]
   * rather than [only_provable].
   *)
  Global Instance into_pure_only_provable P : @IntoPure PROP [| P |] P.
  Proof. by rewrite/IntoPure/only_provable bi.affinely_elim. Qed.
  Global Instance from_pure_only_provable P : @FromPure PROP true [| P |] P.
  Proof. by rewrite/FromPure/only_provable. Qed.
  Global Instance into_wand_only_provable p (P : Prop) Q :
    Absorbing Q → @IntoWand PROP p false (∀ _ : P, Q) [| P |] Q.
  Proof.
    intros. rewrite/IntoWand. rewrite (bi.intuitionistically_if_elim p) /=.
    by rewrite -only_provable_wand_forall.
  Qed.
  Global Instance from_and_only_provable P Q :
    @FromAnd PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromAnd only_provable_and. Qed.
  Global Instance into_and_only_provable p P Q :
    @IntoAnd PROP p [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoAnd only_provable_and. Qed.
  Global Instance from_sep_only_provable P Q :
    @FromSep PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromSep only_provable_sep. Qed.
  Global Instance into_sep_only_provable P Q :
    @IntoSep PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoSep only_provable_sep. Qed.
  Global Instance from_or_only_provable P Q :
    @FromOr PROP [| P ∨ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromOr only_provable_or. Qed.
  Global Instance into_or_only_provable P Q :
    @IntoOr PROP [| P ∨ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoOr only_provable_or. Qed.
  Global Instance from_exist_only_provable {A} (P : A → Prop) :
    @FromExist PROP A [| ∃ x, P x |] (λ a, [| P a |]).
  Proof. by rewrite/FromExist only_provable_exist. Qed.
  Global Instance into_exist_only_provable {A} (P : A → Prop) :
    @IntoExist PROP A [| ∃ x, P x |] (λ a, [| P a |]).
  Proof. by rewrite/IntoExist only_provable_exist. Qed.
  Global Instance into_forall_only_provable {A} (P : A → Prop) :
    @IntoForall PROP A [| ∀ x, P x |] (λ a, [| P a |]).
  Proof. by rewrite/IntoForall only_provable_forall. Qed.
End proofmode.
Typeclasses Opaque only_provable.
Global Opaque only_provable.	(** Less important *)

Section with_PROP.
Context {PROP : bi}.

Lemma wandSP_only_provableL : forall (P : Prop) (Q R : PROP),
    P ->
    Q |-- R ->
    [| P |] -* Q |-- R.
Proof.
  iIntros (???? HQR) "HPQ". iApply HQR. by iApply "HPQ".
Qed.

Lemma wandSP_only_provableR : forall (A : Prop) (B C : PROP),
    (A -> B |-- C) ->
    B |-- [| A |] -* C.
Proof.
  iIntros (??? HC) "HB %". by iApply (HC with "HB").
Qed.
End with_PROP.
End with_notation.
