(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import invariants cancelable_invariants.
From iris.proofmode Require Import tactics.

From bedrock.lang.cpp Require Import logic.pred.

Set Default Proof Using "Type".

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

  Section with_invG.
    Context `{!invG Σ}.

    (* the names of invariants *)
    Definition iname : Set := namespace.

    Bind Scope string_scope with iname.

    (* named invariants *)
    (* mpred version of [inv]: s/inv/Inv;s/iProp Σ/mpred *)
    Definition Inv : namespace → mpred → mpred := inv.

    Lemma Inv_alloc : forall n I,
      |>I |-- |={⊤}=> Inv n I.
    Proof using . intros. by apply inv_alloc. Qed.

    Global Instance: Persistent (Inv n P).
    Proof using . apply _. Qed.

    Global Instance: Affine (Inv n P).
    Proof using . apply _. Qed.
  End with_invG.

  Section with_cinvG.
    Context `{!cinvG Σ}.
    (* mpred version of [cinv]: s/cinv/TInv;s/iProp Σ/mpred *)
    Definition TInv : namespace → gname → mpred → mpred := cinv.

    Definition TInv_own : gname → frac → mpred := cinv_own.

    (* a stronger invariant allocation lemma. This allows one to:
      - pick the ghost name γ to be outside of a set G (γ ∉ G)
      - delay picking the invariant I until γ is allocated, so that I can
        depend on γ. Notably, one can put the invariant token TInv_own γ q
        inside the invariant I. *)
    Lemma TInv_alloc_cofinite : forall (G: gset gname) M N,
      |-- |={M}=> Exists γ, ⌜ γ ∉ G ⌝ ** TInv_own γ 1%Qp **
                            ∀ I, ▷ I ={M}=∗ TInv N γ I.
    Proof. by apply cinv_alloc_cofinite. Qed.

    (* Even stronger: stronger constraints on γ can be picked
      Also see cinv_alloc_strong_open, the invariant can be allocated but
      establishing its content can be delayed. It can be added when needed. *)
    Lemma TInv_alloc_strong : forall (F : gname → Prop) M N,
      pred_infinite F →
      |-- |={M}=> ∃ γ, ⌜ F γ ⌝ ∗ TInv_own γ 1 ∗ ∀ I, ▷ I ={M}=∗ TInv N γ I.
    Proof. apply cinv_alloc_strong. Qed.

    Corollary TInv_alloc_ghost_named_inv : forall M N I,
      (∀ γ : gname, I γ) |--
      |={M}=> Exists γ, TInv N γ (I γ) ** TInv_own γ 1%Qp.
    Proof.
      intros. iIntros "I".
      iMod (TInv_alloc_cofinite empty M N) as (γ ?) "[HO HI]".
      iSpecialize ("I" $! γ).
      iMod ("HI" $! (I γ) with "[$I]") as "HI".
      iIntros "!>". eauto with iFrame.
    Qed.

    Lemma TInv_alloc : forall M N I,
      |>I |-- |={M}=> Exists γ, TInv N γ I ** TInv_own γ 1%Qp.
    Proof using . intros. apply cinv_alloc. Qed.

    Global Instance TInv_persistent : Persistent (TInv Ns γ P).
    Proof using . apply _. Qed.
    Global Instance TInv_affine : Affine (TInv Ns γ P).
    Proof using . apply _. Qed.
    Global Instance TInv_own_fractional γ : Fractional (TInv_own γ).
    Proof. apply _. Qed.
    Global Instance TInv_own_as_fractional γ q :
      AsFractional (TInv_own γ q) (TInv_own γ) q.
    Proof. apply _. Qed.

    Lemma TInv_cancel M N γ I :
      ↑N ⊆ M ->
      TInv N γ I |-- TInv_own γ 1%Qp -* |={M}=> |>I.
    Proof using . apply cinv_cancel. Qed.

    #[deprecated(since="20200824", note="Use TInv_cancel instead")]
    Lemma TInv_delete M N γ I :
      ↑N ⊆ M ->
      TInv N γ I ** TInv_own γ 1%Qp |-- |={M}=> |>I.
    Proof. intros. iIntros "[#? ?]". iApply TInv_cancel; eauto. Qed.
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

    Lemma TInv_acc_strong E N γ p P :
      ↑N ⊆ E →
      TInv N γ P |-- (TInv_own γ p ={E,E∖↑N}=∗
                            ((|>P) ** TInv_own γ p **
                            (Forall (E' : coPset),
                              ((|>P ∨ TInv_own γ 1) ={E',↑N ∪ E'}=∗ True)))).
    Proof using . apply cinv_acc_strong. Qed.

  End with_cinvG.
End with_Σ.

#[deprecated(since="20200824", note="Use Inv_alloc instead")]
Notation Inv_new := Inv_alloc (only parsing).

#[deprecated(since="20200824", note="Use TInv_alloc instead")]
Notation TInv_new := TInv_alloc (only parsing).

#[deprecated(since="20200824", note="Use TInv_acc_strong instead")]
Notation Tinv_open_strong := TInv_acc_strong (only parsing).
