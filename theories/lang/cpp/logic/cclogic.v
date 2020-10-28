(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.prelude.base.

From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import invariants cancelable_invariants.
From iris.proofmode Require Import tactics.

From bedrock.lang.cpp Require Import logic.pred.


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
    (P -* |={ ⊤ ∖ ↑N, ⊤  }=> Q) ** (|={⊤, ⊤ ∖ ↑N}=> P) |-- |={⊤}=> Q.
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

  Definition iname : Set := namespace.

  Section with_cinvG.
    Context `{!cinvG Σ}.

    Corollary cinv_alloc_ghost_named_inv : forall M N I,
      (∀ γ : gname, I γ) |--
      |={M}=> Exists γ, cinv N γ (I γ) ** cinv_own γ 1%Qp.
    Proof.
      intros. iIntros "I".
      iMod (cinv_alloc_cofinite empty M N) as (γ ?) "[HO HI]".
      iSpecialize ("I" $! γ).
      iMod ("HI" $! (I γ) with "[$I]") as "HI".
      iIntros "!>". eauto with iFrame.
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
  End with_cinvG.
End with_Σ.
