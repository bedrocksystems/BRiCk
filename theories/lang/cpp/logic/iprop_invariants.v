(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is derived from code original to the Iris project. That
 * original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/iris/base_logic/lib/invariants.v
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/iris/base_logic/lib/cancelable_invariants.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/LICENSE-CODE
 *)

(* NOTES FOR MAINTAINER: this is the iProp instances for invariants. This is
  needed when mpred is still iProp. Once mpred is fixed to monPred, then this
  can be removed. *)
From iris.proofmode Require Import tactics.

Require Import bedrock.lang.bi.cancelable_invariants.
Require Import bedrock.lang.bi.invariants.
Require Import bedrock.lang.cpp.logic.iprop_own.

(*** Invariants for iProp **)
(* Copy from
  https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/iris/base_logic/lib/invariants.v *)
Section inv.
  Context `{!invG Σ}.
  Implicit Types (P : iProp Σ).

  #[local] Lemma own_inv_to_inv M P: own_inv M P -∗ inv M P.
  Proof.
    iIntros "#I". rewrite inv_eq. iIntros (E H).
    iPoseProof (own_inv_acc with "I") as "H"; eauto.
  Qed.

  Lemma inv_alloc N E P : ▷ P ={E}=∗ inv N P.
  Proof.
    iIntros "HP". iApply own_inv_to_inv.
    iApply (own_inv_alloc N E with "HP").
  Qed.

  Lemma inv_alloc_open N E P :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (?). iMod own_inv_alloc_open as "[HI $]"; first done.
    iApply own_inv_to_inv. done.
  Qed.
End inv.

(*** Cancelable invariants for iProp *)
Typeclasses Transparent cinv_own cinv.
(* Copy from
  https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/iris/base_logic/lib/cancelable_invariants.v *)
Section cinv.
  Context `{!invG Σ, !cinvG Σ}.
  Implicit Types (P : iProp Σ).
  (*** Allocation rules. *)
  (** The "strong" variants permit any infinite [I], and choosing [P] is delayed
  until after [γ] was chosen.*)
  Lemma cinv_alloc_strong (I : gname → Prop) E N :
    pred_infinite I →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P.
  Proof.
    iIntros (?). iMod (own_alloc_strong 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P) "HP".
    iMod (inv_alloc N _ (P ∨ cinv_own γ 1) with "[HP]"); eauto.
  Qed.

  (** The "open" variants create the invariant in the open state, and delay
  having to prove [P].
  These do not imply the other variants because of the extra assumption [↑N ⊆ E]. *)
  Lemma cinv_alloc_strong_open (I : gname → Prop) E N :
    pred_infinite I →
    ↑N ⊆ E →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P,
      |={E,E∖↑N}=> cinv N γ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (??). iMod (own_alloc_strong 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P).
    iMod (inv_alloc_open N _ (P ∨ cinv_own γ 1)) as "[Hinv Hclose]"; first by eauto.
    iIntros "!>". iFrame. iIntros "HP". iApply "Hclose". iLeft. done.
  Qed.

  Lemma cinv_alloc_cofinite (G : gset gname) E N :
    ⊢ |={E}=> ∃ γ, ⌜ γ ∉ G ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P.
  Proof.
    apply cinv_alloc_strong. apply (pred_infinite_set (C:=gset gname))=> E'.
    exists (fresh (G ∪ E')). apply not_elem_of_union, is_fresh.
  Qed.

  Lemma cinv_alloc E N P : ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    iIntros "HP". iMod (cinv_alloc_cofinite ∅ E N) as (γ _) "[Hγ Halloc]".
    iExists γ. iFrame "Hγ". by iApply "Halloc".
  Qed.

  Lemma cinv_alloc_open E N P :
    ↑N ⊆ E → ⊢ |={E,E∖↑N}=> ∃ γ, cinv N γ P ∗ cinv_own γ 1 ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (?). iMod (cinv_alloc_strong_open (λ _, True)) as (γ) "(_ & Htok & Hmake)"; [|done|].
    { apply pred_infinite_True. }
    iMod ("Hmake" $! P) as "[Hinv Hclose]". iIntros "!>". iExists γ. iFrame.
  Qed.

  Corollary cinv_alloc_ghost_named_inv E N (I : gname → iProp _) :
    (∀ γ , I γ) ⊢ |={E}=> ∃ γ, cinv N γ (I γ) ∗ cinv_own γ 1.
  Proof.
    iIntros "I".
    iMod (cinv_alloc_cofinite empty E N) as (γ ?) "[HO HI]".
    iSpecialize ("I" $! γ).
    iMod ("HI" $! (I γ) with "[$I]") as "HI".
    iIntros "!>". eauto with iFrame.
  Qed.
End cinv.

Typeclasses Opaque cinv_own cinv.
