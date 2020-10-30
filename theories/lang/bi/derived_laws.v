(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(** *)

From iris.bi Require Import bi.
From iris.proofmode Require Import tactics.
From bedrock.lang.bi Require only_provable.

(**
Derived BI laws, similarly to iris.bi.derived_laws.

They should be upstreamed if appropriate.
When upstreaming, add a comment (with the upstream name if different).
When bumping Iris, drop lemmas that are now upstream.
*)

Module bi.
Export iris.bi.bi.bi.

Section derived_laws.
  Context {PROP : bi}.

  (* Upstream as [exist_exist], https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/552 *)
  Lemma exist_exist {A B} (Φ : A → B → PROP) :
    (∃ a b, Φ a b) ⊣⊢ (∃ b a, Φ a b).
  Proof. iSplit; iDestruct 1 as (??) "H"; eauto. Qed.

  (* Upstream as [exist_forall], ditto. *)
  Lemma exist_forall {A B} (Φ : A → B → PROP) :
    (∃ a, ∀ b, Φ a b) ⊢ (∀ b, ∃ a, Φ a b).
  Proof. iDestruct 1 as (a) "H". iIntros (b). iExists a. by iApply "H". Qed.

  (** Useful when proving Fractional instances involving existentials. *)
  Lemma exist_sep_1 {A} (Φ Ψ : A → PROP) : (∃ a, Φ a ∗ Ψ a) ⊢ (∃ a, Φ a) ∗ (∃ a, Ψ a).
  Proof.
    rewrite bi.sep_exist_r. f_equiv=>a. f_equiv.
    apply bi.exist_intro.
  Qed.

  Lemma exist_sep_2 {A} (Φ Ψ : A → PROP) :
    (∀ a1 a2, Φ a1 ⊢ Ψ a2 -∗ ⌜a1 = a2⌝) →
    (∃ a, Φ a) ∗ (∃ a, Ψ a) ⊢ (∃ a, Φ a ∗ Ψ a).
  Proof.
    iIntros (Hag) "[A1 A2]".
    iDestruct "A1" as (a1) "Φ".
    iDestruct "A2" as (a2) "Ψ".
    iDestruct (Hag with "Φ Ψ") as %->.
    iExists a2; iFrame.
  Qed.

  Lemma exist_sep {A} (Φ Ψ : A → PROP)
    (Hag : ∀ a1 a2, Φ a1 ⊢ Ψ a2 -∗ ⌜a1 = a2⌝) :
    (∃ a, Φ a ∗ Ψ a) ⊣⊢ (∃ a, Φ a) ∗ (∃ a, Ψ a).
  Proof. apply (anti_symm (⊢)); eauto using exist_sep_1, exist_sep_2. Qed.

  Lemma sep_unique_exist {A} (P Q R : A → PROP)
    (Hag : ∀ a1 a2, Q a1 ⊢ R a2 -∗ ⌜ a1 = a2 ⌝)
    (HPQ : ∀ a, P a ⊣⊢ Q a ∗ R a) :
    (∃ a, P a) ⊣⊢ (∃ a, Q a) ∗ (∃ a, R a).
  Proof. setoid_rewrite HPQ. apply exist_sep, Hag. Qed.

  Lemma exist_and_1 {A} (Φ Ψ : A → PROP) : (∃ a, Φ a ∧ Ψ a) ⊢ (∃ a, Φ a) ∧ (∃ a, Ψ a).
  Proof.
    rewrite bi.and_exist_r. f_equiv=>a. f_equiv.
    apply bi.exist_intro.
  Qed.

  Lemma exist_and_2 {A} (Φ Ψ : A → PROP)
    (Hag : ∀ a1 a2, Φ a1 ∧ Ψ a2 ⊢ ⌜a1 = a2⌝) :
    (∃ a, Φ a) ∧ (∃ a, Ψ a) ⊢ (∃ a, Φ a ∧ Ψ a).
  Proof.
    rewrite bi.and_exist_l. f_equiv=> a1.
    rewrite bi.and_exist_r.
    iDestruct 1 as (a2) "H".
    iSplit; last by iDestruct "H" as "[_ $]".
    by iDestruct (Hag with "[H]") as %->; last iDestruct "H" as "[$ _]".
  Qed.

  Lemma exist_and {A} (Φ Ψ : A → PROP)
    (Hag : ∀ a1 a2, Φ a1 ∧ Ψ a2 ⊢ ⌜a1 = a2⌝) :
    (∃ a, Φ a ∧ Ψ a) ⊣⊢ (∃ a, Φ a) ∧ (∃ a, Ψ a).
  Proof. apply (anti_symm (⊢)); eauto using exist_and_1, exist_and_2. Qed.

  Lemma and_unique_exist {A} (P Q R : A → PROP)
    (Hag : ∀ a1 a2, Q a1 ∧ R a2 ⊢ ⌜ a1 = a2 ⌝)
    (HPQ : ∀ a, P a ⊣⊢ Q a ∧ R a) :
    (∃ a, P a) ⊣⊢ (∃ a, Q a) ∧ (∃ a, R a).
  Proof. setoid_rewrite HPQ. apply exist_and, Hag. Qed.

  (* See https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/556 *)
  Lemma intuitionistic_sep_dup (P : PROP) `{!Persistent P, !Affine P} :
    P ⊣⊢ P ∗ P.
  Proof.
    apply (anti_symm (⊢)).
    by rewrite -{1}(bi.intuitionistic_intuitionistically P)
      bi.intuitionistically_sep_dup bi.intuitionistically_elim.
    by rewrite {1}(affine P) left_id.
  Qed.

  Lemma persistent_sep_distr_l (P Q R : PROP) `{!Persistent P, !Affine P} :
    P ∗ Q ∗ R ⊣⊢ (P ∗ Q) ∗ (P ∗ R).
  Proof.
    rewrite {1}(intuitionistic_sep_dup P).
    iSplit; iIntros "[[$$] [$$]]".
  Qed.

  Lemma persistent_sep_distr_r (P Q R : PROP) `{!Persistent R, !Affine R} :
    (P ∗ Q) ∗ R ⊣⊢ (P ∗ R) ∗ (Q ∗ R).
  Proof. rewrite !(comm bi_sep _ R). exact: persistent_sep_distr_l. Qed.

  Lemma persistent_sep_and_distr_l P Q1 Q2 `{!Persistent P} `{!Affine P} :
    P ∗ (Q1 ∧ Q2) ⊣⊢@{PROP}
    (P ∗ Q1) ∧ (P ∗ Q2).
  Proof.
    iSplit. by iIntros "[$ $]".
    iIntros "H"; iSplit. by iDestruct "H" as "[[$ _] _]".
    iSplit.
    iDestruct "H" as "[[_ $]_]".
    iDestruct "H" as "[_ [_ $]]".
  Qed.

  Lemma persistent_sep_and_distr_r {P1 P2 Q} `{!Persistent Q} `{!Affine Q} :
    (P1 ∧ P2) ∗ Q ⊣⊢@{PROP}
    (P1 ∗ Q) ∧ (P2 ∗ Q).
  Proof. rewrite !(comm bi_sep _ Q). exact: persistent_sep_and_distr_l. Qed.
End derived_laws.

Section only_provable_derived_laws.
  Import only_provable.
  Context {PROP : bi}.

  Lemma exist_sep_only_provable {A} (Φ Ψ : A → PROP)
    (Hag : ∀ a1 a2, Φ a1 ⊢ Ψ a2 -∗ [| a1 = a2 |]) :
    (∃ a, Φ a ∗ Ψ a) ⊣⊢ (∃ a, Φ a) ∗ (∃ a, Ψ a).
  Proof.
    apply exist_sep.
    iIntros (??) "Q R". by iDestruct (Hag with "Q R") as %->.
  Qed.

  Lemma sep_unique_exist_only_provable {A} (P Q R : A → PROP)
    (Hag : ∀ a1 a2, Q a1 ⊢ R a2 -∗ [| a1 = a2 |]) :
    (∀ a, P a ⊣⊢ Q a ∗ R a) →
    (∃ a, P a) ⊣⊢ (∃ a, Q a) ∗ (∃ a, R a).
  Proof.
    apply sep_unique_exist.
    iIntros (??) "Q R". by iDestruct (Hag with "Q R") as %->.
  Qed.

  Lemma exist_and_only_provable {A} (Φ Ψ : A → PROP)
    (Hag : ∀ a1 a2, Φ a1 ∧ Ψ a2 ⊢ [| a1 = a2 |]) :
    (∃ a, Φ a ∧ Ψ a) ⊣⊢ (∃ a, Φ a) ∧ (∃ a, Ψ a).
  Proof.
    apply exist_and.
    iIntros (??) "Q". by iDestruct (Hag with "Q") as %->.
  Qed.

  Lemma and_unique_exist_only_provable {A} (P Q R : A → PROP)
    (Hag : ∀ a1 a2, Q a1 ∧ R a2 ⊢ [| a1 = a2 |]) :
    (∀ a, P a ⊣⊢ Q a ∧ R a) →
    (∃ a, P a) ⊣⊢ (∃ a, Q a) ∧ (∃ a, R a).
  Proof.
    apply and_unique_exist.
    iIntros (??) "Q". by iDestruct (Hag with "Q") as %->.
  Qed.

  Lemma exist_and_absorb_agree {A : Type} (Θ Φ Ψ : A → PROP)
      `{∀ a, Affine (Θ a), ∀ a, Persistent (Θ a)} :
    (∀ a1 a2, <absorb> Θ a1 ∗ <absorb> Θ a2 ⊢ ⌜ a1 = a2 ⌝) →
    (∃ a, Θ a ∗ (Φ a ∧ Ψ a)) ⊣⊢ (∃ a, Θ a ∗ Φ a) ∧ (∃ a, Θ a ∗ Ψ a).
  Proof.
    intros Hag.
    apply and_unique_exist => [a1 a2 | a];
      last by rewrite persistent_sep_and_distr_l.
    iIntros "H". iApply Hag. iApply bi.persistent_and_sep_1; iSplit.
    - by iDestruct "H" as "[[$ _] _]".
    - by iDestruct "H" as "[_ [$ _]]".
  Qed.

  Lemma exist_and_agree {A : Type} (Θ Φ Ψ : A → PROP)
      `{∀ a, Affine (Θ a), ∀ a, Persistent (Θ a)}
    (Hagree : ∀ a1 a2, Θ a1 ∗ Θ a2 ⊢ [| a1 = a2 |]) :
    (∃ a, Θ a ∗ (Φ a ∧ Ψ a)) ⊣⊢ (∃ a, Θ a ∗ Φ a) ∧ (∃ a, Θ a ∗ Ψ a).
  Proof.
    apply (anti_symm _).
    - rewrite -exist_and_1. f_equiv=>a. iDestruct 1 as "[$ $]".
    - rewrite and_exist_l. f_equiv=> a2. iIntros "H".
      iAssert (Θ a2) as "#Ha"; first by iDestruct "H" as "[_ [$ _]]".
      iFrame "Ha". iSplit; last by iDestruct "H" as "[_ [_ $]]".
      rewrite and_exist_r. iDestruct "H" as (a1) "[[Ha2 R] _]".
      by iDestruct (Hagree a1 a2 with "[$Ha2]") as "->".
  Qed.
End only_provable_derived_laws.
End bi.
