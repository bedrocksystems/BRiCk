Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Coq.Sorting.Permutation.
From Coq.QArith Require Import QArith Qcanon.
Require Import Coq.QArith.Qfield.
From Coq.micromega Require Import
     QMicromega Psatz.

Require Import Coq.ssr.ssrbool.

From Coq.Classes Require Import
     RelationClasses Morphisms DecidableClass.

From iris.base_logic.lib Require Import
     fancy_updates invariants cancelable_invariants own wsat.
Import invG.
From iris.algebra Require Import excl auth.

From iris.proofmode Require Import tactics.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
      Semantics Logic Operator PLogic Wp Call.
From Cpp Require Import ChargeCompat.

Require Import ExtLib.Data.Member.

Module Type cclogic.

  Section with_Σ.
    Context `{!invG Σ}.

    Local Notation mpred := (mpred Σ) (only parsing).

    (** Unsound axioms **)
    (* This should only be possible for wp's for a given mask *)
    Axiom add_fupd : forall (P : mpred), (|={ ⊤, ⊤ }=> P)%I |-- P.
    (* todo(gmm): still need thisThis should not be possible. Laters should instead be stripped by execution *)
    Axiom add_later : forall (P : mpred), (|> P) |-- P.
  End with_Σ.

  Module GhostState.

    Section with_Σ.
    Context `{!invG Σ}.

    Local Notation mpred := (mpred Σ) (only parsing).

    Section with_Σ'.
      Context `{!inG Σ A}.

      Lemma own_alloc_frame (R : A) : forall P Q,
          ✓ R ->
          (forall (γ : gname), P ** own γ R |-- Q) ->
          P |-- Q.
      Proof.
        intros.
        iIntros "HP".
        iApply add_fupd.
        iMod (own_alloc R) as (γ) "H".
        { by apply H. }
        iModIntro.
        iApply H0.
        iFrame.
      Qed.

    End with_Σ'.

    Lemma viewshift_example (P Q : mpred) (N : namespace) :
      (P -* |={ ⊤ ∖ ↑N, ⊤  }=> Q) ** (|={⊤, ⊤ ∖ ↑N}=> P)%I |--  Q.
    Proof.
      (* Introduce hypotheses into context by destructing separation conjunct *)
      iIntros "[HPQ HP]".
      (* Start shifting *)
      iApply add_fupd.
      (* Construct hypothesis granularity *)
      iApply (fupd_trans _ (⊤ ∖ ↑N)).
      (* Resolve second shift *)
      iApply "HPQ".
      (* Resolve first shift *)
      iApply "HP".
    Qed.

    Lemma invariant_example (P : mpred) `{!Persistent P} (N : namespace) : P |-- |> P.
    Proof.
      iIntros "HP".
      (* wp_shift_anywhere *)
      iApply add_fupd.
      (* Allocate invariant, using current HP and create new HP (in persistnet context)  *)
      iMod (inv_alloc N _ (P) with "[HP]") as "#HP".
      { iNext. eauto. }         (* Solve the goal *)
      (* Open invariants in namespace N *)
      iInv N as "#HP'".
      (* Cancel the reflexive shift *)
      iModIntro.
      (* Solve the invariant closing requirement and the goal separately *)
      iSplitR.
      - iApply "HP'".
      - iModIntro. iNext. iApply "HP'".
    Qed.

    End with_Σ.
  End GhostState.
  Export GhostState.

  Module Invariants.
    (* notes:
     * - These can be encoded using ghost state.
     *)

    Section with_Σ.
      Context `{!invG Σ}.

      Local Notation mpred := (mpred Σ) (only parsing).

      (* the names of invariants *)
      Definition iname : Set := namespace.

      (* named invariants *)
      Definition Inv := inv.

      Lemma Inv_new : forall n I,
          |>I |-- Inv n I.
      Proof.
        intros. iIntros "HI".
        iApply add_fupd.
        iApply (inv_alloc with "HI").
      Qed.

      Lemma Inv_dup : forall (n : iname) I, Inv n I -|- Inv n I ** Inv n I.
      Proof.
        intros.
        iSplit.
        - iIntros "#HI". eauto.
        - iIntros "[HI _]". eauto.
      Qed.

      Lemma Inv_drop : forall (n : iname) I, Inv n I |-- empSP.
      Proof. eauto. Qed.

      (* Move this somewhere else? *)
      Lemma Inv_new_imp N I : forall (P R Q : mpred),
          (P |-- (|>I) ** R) ->
          Inv N I ** R |-- Q ->
          P |-- Q.
      Proof.
        intros.
        rewrite H. rewrite <- H0. rewrite <- (Inv_new N I).
        iIntros "[$ $]".
      Qed.

      Section with_Σ'.
        Context `{!cinvG Σ}.

        Definition TInv N γ (I : mpred) : mpred := cinv N γ I.

        Definition TInv_own γ q : mpred := cinv_own γ q.

        Lemma TInv_new : forall N I,
            |>I |-- Exists γ, TInv N γ I ** TInv_own γ 1%Qp.
        Proof.
          intros. iIntros "HI".
          iApply add_fupd.
          unfold TInv. unfold TInv_own.
          by iApply (cinv_alloc with "[HI]").
        Qed.

        Lemma TInv_dup : forall (N : iname) γ  I,
            TInv N γ I -|- TInv N γ I ** TInv N γ I.
        Proof.
          intros.
          iSplit.
          - iIntros "#HI". eauto.
          - iIntros "[HI _]". eauto.
        Qed.
        Lemma TInv_drop : forall (N : iname) γ I, TInv N γ I |-- empSP.
        Proof. eauto. Qed.

        Lemma TInv_delete N γ I : TInv N γ I ** TInv_own γ 1%Qp |-- |>I.
        Proof.
          intros.
          iIntros "[#Hinv Hq]".
          iApply add_fupd.
          unfold TInv.
          iApply cinv_cancel; eauto.
        Qed.

        Lemma TInv_new_imp N I : forall (P R Q : mpred),
          (P |-- (|>I) ** R) ->
          Exists γ, (TInv N γ I ** TInv_own γ 1%Qp) ** R  |-- Q ->
          P |-- Q.
        Proof.
          intros.
          rewrite H. rewrite <- H0.
          rewrite -> (TInv_new N I).
          iIntros "[H $]".
          iDestruct "H" as (γ) "H". eauto.
        Qed.

        (* Lemma variant of Iris lemma "cing_open_strong" that has not been bumped *)
        Lemma cinv_open_stronger E N γ p P :
          ↑N ⊆ E →
          cinv N γ P -* (cinv_own γ p ={E,E∖↑N}=∗
          ((|>P) ** cinv_own γ p ** (Forall (E' : coPset), ((|>(P ∨ cinv_own γ 1)) ={E',↑N ∪ E'}=∗ True)))).
        Proof. Admitted.

      End with_Σ'.
    End with_Σ.
  End Invariants.
  Import Invariants.
  Export Invariants.
  
End cclogic.

Declare Module CCL : cclogic.

Export CCL.
