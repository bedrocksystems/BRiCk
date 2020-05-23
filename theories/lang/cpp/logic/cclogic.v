(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.

Require Import Coq.ssr.ssrbool.

From Coq.Classes Require Import
     RelationClasses Morphisms DecidableClass.

From iris.base_logic.lib Require Import
      fancy_updates invariants cancelable_invariants own wsat.
Import invG.
From iris.algebra Require Import excl auth.

From iris.proofmode Require Import tactics.

Require Import bedrock.ChargeCompat.
Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp Require Import
     logic.pred.

Bind Scope string_scope with namespace.

Section with_Σ.
  Context `{Σ : cpp_logic, !invG Σ}.

  Section with_Σ'.
    Context `{!inG Σ A}.

    Lemma own_alloc_frame (R : A) : forall P Q,
        ✓ R ->
        (forall (γ : gname), P ** own γ R |-- Q) ->
        P |-- |==> Q.
    Proof using .
      intros.
      iIntros "HP".
      iMod (own_alloc R) as (γ) "H".
      { by apply H. }
      iModIntro.
      iApply H0.
      iFrame.
    Qed.

  End with_Σ'.

  Example viewshift_example (P Q : mpred) (N : namespace) :
    (P -* |={ ⊤ ∖ ↑N, ⊤  }=> Q) ** (|={⊤, ⊤ ∖ ↑N}=> P)%I |-- |={⊤}=> Q.
  Proof using .
    (* Introduce hypotheses into context by destructing separation conjunct *)
    iIntros "[HPQ HP]".
    (* Construct hypothesis granularity *)
    iMod "HP".
    (* Resolve second shift *)
    iApply "HPQ".
    (* Resolve first shift *)
    iApply "HP".
  Qed.

  Context `{!invG Σ}.

  (* the names of invariants *)
  Definition iname : Set := namespace.

  Bind Scope string_scope with iname.

  (* named invariants *)
  Definition Inv := inv.

  Lemma Inv_new : forall n I,
      |>I |-- (|={⊤}=> Inv n I)%I.
  Proof using .
    intros. iIntros "HI".
    iApply (inv_alloc with "HI").
  Qed.

  Global Instance: Persistent (Inv n P).
  Proof using .
    intros. red. iIntros "#HI". eauto.
  Qed.

  Global Instance: Affine (Inv n P).
  Proof using . red. eauto. Qed.

  Section with_Σ'.
    Context `{!cinvG Σ}.

    Definition TInv N γ (I : mpred) : mpred := cinv N γ I.

    Definition TInv_own γ q : mpred := cinv_own γ q.

    Lemma TInv_new : forall M N I,
        |>I |-- (|={M}=> Exists γ, TInv N γ I ** TInv_own γ 1%Qp)%I.
    Proof using .
      intros. iIntros "HI".
      unfold TInv. unfold TInv_own.
        by iApply (cinv_alloc with "[HI]").
    Qed.

    Global Instance: Persistent (TInv Ns γ P).
    Proof using . red. intros; iIntros "#HI". eauto. Qed.
    Global Instance: Affine (TInv Ns γ P).
    Proof using . red. eauto. Qed.

    Lemma TInv_delete M N γ I :
      ↑N ⊆ M ->
      TInv N γ I ** TInv_own γ 1%Qp |-- (|={M}=> |>I)%I.
    Proof using .
      intros.
      iIntros "[#Hinv Hq]".
      unfold TInv.
      iApply cinv_cancel; eauto.
    Qed.


(*
    Lemma cinv_open_stronger E N γ p P :
      ↑N ⊆ E →
      cinv N γ P ⊢ (cinv_own γ p ={E,E∖↑N}=∗
                    ((|>P) ** cinv_own γ p ** (Forall (E' : coPset), ((|>(P ∨ cinv_own γ 1)) ={E',↑N ∪ E'}=∗ True)))).
    Proof.
      iIntros (?) "Hinv Hown".
      unfold cinv. (* iDestruct "Hinv" as (P') "[#HP' Hinv]". *)
      iPoseProof (inv_acc (↑ N) N _ with "Hinv") as "H"; first done.
      rewrite difference_diag_L.
      iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
      rewrite left_id_L -union_difference_L //. iMod "H" as "[[HP | >HP] H]".
      - iModIntro. iFrame. iDestruct ("HP'" with "HP") as "HP". iFrame. iModIntro.
        iIntros (E') "HP".
        iPoseProof (fupd_mask_frame_r _ _ E' with "(H [HP])") as "H"; first set_solver.
        { iDestruct "HP" as "[HP | >Hown]".
          iLeft. by iApply "HP'".
          eauto.
        }
          by rewrite left_id_L.
      - iDestruct (cinv_own_1_l with "HP Hown") as %[].
    Qed.
*)

    Lemma Tinv_open_strong E N γ p P :
      ↑N ⊆ E →
      cinv N γ P |--
           (cinv_own γ p ={E,E∖↑N}=∗
                                  ((|>P) ** cinv_own γ p ** (Forall (E' : coPset), ((|>P ∨ cinv_own γ 1) ={E',↑N ∪ E'}=∗ True))))%I.
    Proof using . iIntros (?) "#Hinv Hown". iApply cinv_acc_strong =>//. Qed.

  End with_Σ'.
End with_Σ.
