(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.base_logic.lib.wsat.
Import invG.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
    pred path_pred heap_pred wp.
Require Import bedrock.lang.cpp.heap_notations.
Require Import bedrock.lang.cpp.logic.atomics.

Require Import iris.proofmode.tactics.

Section cmpxchg_derived.
  Context `{Σ : cpp_logic thread_info, !invG Σ} {resolve:genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Local Notation primR := (@primR _ _ resolve) (only parsing).
  Local Notation wp_atom' := (@wp_atom _ Σ resolve M ti) (only parsing).

  (* A successful SC compare and exchange n *)
  (* It succeeds because the location p has the expected value v, which is
    stored in expected. *)
  Lemma wp_atom_compare_exchange_n_cst_suc :
    forall p expected_p desired weak succmemord failmemord Q ty v,
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      |> ((* pre cond *)
          ((* placeholder for the expected value, which is v *)
           _eqv expected_p |-> primR ty 1 v **
          (* latest value of p, which is also v, because this is successful *)
           _eqv p |-> primR ty 1 v) **
          (* post cond *)
          (_eqv expected_p |-> primR ty 1 v **
          (* afterwards, val_pp has value desired *)
            _eqv p |-> primR ty 1 desired -* Q (Vbool true)))
      |-- wp_atom' AO__atomic_compare_exchange_n ty
                  (p::succmemord::expected_p::failmemord::desired::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & [Pre1 Pre2] & Post)".
    iApply wp_atom_compare_exchange_n_cst. iFrame.
    iNext. iSplit.
    - iIntros "(P1 & P2 & ?)". iApply "Post". iFrame.
    - by iIntros "(_ & _ & %)".
  Qed.

  (* A failed SC strong compare exchange, which tell us that the values are
    truly different. *)
  Lemma wp_atom_compare_exchange_n_cst_fail :
    forall p val_p desired weak succmemord failmemord Q
           (ty : type) v expected_v,
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* we know that the values are different *)
      [| v <> expected_v |] **
      |> ((* precond *)
          ((* before, val_p stores the value expected_v to be compared *)
           _eqv val_p |-> primR ty 1 expected_v **
           _eqv p |-> primR ty 1 v) **
          (* post cond *)
          (* afterwards, val_p stores the value read v, which is the latest one
              due to failmemord being SC *)
          (_eqv val_p |-> primR ty 1 v **
           _eqv p |-> primR ty 1 v -* Q (Vbool false)))
      |-- wp_atom' AO__atomic_compare_exchange_n ty
                  (p::succmemord::val_p::failmemord::desired::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & % & [Pre1 Pre2] & Post)".
    iApply wp_atom_compare_exchange_n_cst. iFrame.
    iNext. iSplit.
    - iIntros "(_ & _ & %)". by subst.
    - iIntros "(P1 & P2 & %)". iApply "Post". by iFrame.
  Qed.

  (* An SC compare and exchange *)
  Lemma wp_atom_compare_exchange_cst_suc :
    forall q p expected_p desired_p weak succmemord failmemord Q
      (ty : type)
      expected desired,
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      |> ((* pre post *)
          (* before, we know that p and expected_p have the same value *)
          (_eqv expected_p |-> primR ty 1 expected **
           _eqv desired_p |-> primR ty q desired **
           _eqv p |-> primR ty 1 expected) **
          (* afterwards, p is updated to desired *)
          (_eqv expected_p |-> primR ty 1 expected **
           _eqv desired_p |-> primR ty q desired **
           _eqv p |-> primR ty 1 desired -* Q (Vbool true)))
      |-- wp_atom' AO__atomic_compare_exchange ty
                  (p::succmemord::expected_p::failmemord::desired_p::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & Pre & Post)".
    iApply wp_atom_compare_exchange_cst. iFrame.
    iNext. iSplit.
    - iIntros "(P1 & P2 & P3 & _)". iApply "Post". by iFrame.
    - by iIntros "(_ & _ & _ & %)".
  Qed.

  Lemma wp_atom_compare_exchange_cst_fail :
    forall q p expected_p desired_p weak succmemord failmemord Q
      (ty : type)
      actual expected desired,
      expected <> actual ->
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      |> ((_eqv expected_p |-> primR ty 1 expected **
           _eqv desired_p |-> primR ty q desired **
           _eqv p |-> primR ty 1 actual) **
          (_eqv expected_p |-> primR ty 1 actual **
           _eqv desired_p |-> primR ty q desired **
           _eqv p |-> primR ty 1 actual -* Q (Vbool false)))
      |-- wp_atom' AO__atomic_compare_exchange ty
                  (p::succmemord::expected_p::failmemord::desired_p::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & Pre & Post)".
    iApply wp_atom_compare_exchange_cst. iFrame.
    iNext. iSplit.
    - iIntros "(_ & _ & _ & %)". by subst.
    - iIntros "(P1 & P2 & P3 & %)". iApply "Post". by iFrame.
  Qed.
End cmpxchg_derived.
