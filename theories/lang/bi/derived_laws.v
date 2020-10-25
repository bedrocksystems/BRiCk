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

  Lemma sep_exist {A} (Φ Ψ : A → PROP) : (∃ a, Φ a ∗ Ψ a) ⊢ (∃ a, Φ a) ∗ (∃ a, Ψ a).
  Proof.
    rewrite bi.sep_exist_r. f_equiv=>a. f_equiv.
    apply bi.exist_intro.
  Qed.

  (** Useful when proving Fractional instances involving existentials. *)
  Lemma sep_unique_exist {A} (P Q R : A → PROP) :
    (∀ a1 a2, Q a1 ⊢ R a2 -∗ ⌜ a1 = a2 ⌝) →
    (∀ a, P a ⊣⊢ Q a ∗ R a) →
    (∃ a, P a) ⊣⊢ (∃ a, Q a) ∗ (∃ a, R a).
  Proof.
    intros HPQ Hag; iSplit. {
      iDestruct 1 as (a) "H". rewrite -sep_exist Hag. by iExists a.
    }
    iDestruct 1 as "[Q R]"; iDestruct "Q" as (a1) "Q"; iDestruct "R" as (a2) "R".
    iExists a1; iDestruct (HPQ with "Q R") as %->.
    rewrite Hag; iFrame.
  Qed.

  Lemma sep_persistent_dist {P Q R : PROP} `{!Persistent P} `{!Absorbing P} :
    P ∗ Q ∗ R ⊣⊢
    (P ∗ Q) ∗ (P ∗ R).
  Proof.
    rewrite {1}(bi.persistent_sep_dup P).
    iSplit; iIntros "[[$$] [$$]]".
  Qed.
End derived_laws.

Section only_provable_derived_laws.
  Import only_provable.
  Context {PROP : bi}.

  Lemma sep_unique_exist_only_provable {A} (P Q R : A → PROP) :
    (∀ a1 a2, Q a1 ⊢ R a2 -∗ [| a1 = a2 |]) →
    (∀ a, P a ⊣⊢ Q a ∗ R a) →
    (∃ a, P a) ⊣⊢ (∃ a, Q a) ∗ (∃ a, R a).
  Proof.
    intros HPQ. apply sep_unique_exist.
    iIntros (??) "Q R". by iDestruct (HPQ with "Q R") as %->.
  Qed.
End only_provable_derived_laws.
End bi.
