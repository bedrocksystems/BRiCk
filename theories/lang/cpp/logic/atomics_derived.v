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
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Local Notation primR := (@primR _ _ resolve) (only parsing).
  Local Notation wp_atom' := (@wp_atom _ Σ resolve M ti) (only parsing).

  (* A successful SC compare and exchange n *)
  (* It succeeds because the location p has the expected value v, which is
    stored in expected_p. *)
  Lemma wp_atom_compare_exchange_n_cst_suc :
    forall p expected_p desired weak succmemord failmemord Q ty v,
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* private pre-cond *)
      |>  _eqv expected_p |-> primR ty 1 v **
      AU1 << (* public pre-cond: latest value of p is also v, because this is
                successful *)
              _eqv p |-> primR ty 1 v >> @M,∅ (* TODO: masks *)
          << (* public post-cond: latest value is desired *)
              _eqv p |-> primR ty 1 desired,
            COMM (_eqv expected_p |-> primR ty 1 v -* Q (Vbool true)) >>
      |-- wp_atom' AO__atomic_compare_exchange_n ty
                  (p::succmemord::expected_p::failmemord::desired::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & Hex & AU)".
    iApply wp_atom_compare_exchange_n_cst. iFrame.
    iAuIntro1.
    iApply (aacc1_aupd_commit with "AU").
  Abort.

  (* A failed SC strong compare exchange, which tell us that the values are
    truly different. *)
  Lemma wp_atom_compare_exchange_n_cst_fail :
    forall p val_p desired weak succmemord failmemord Q
           (ty : type) v expected_v,
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* we know that the values are different *)
      [| v <> expected_v |] **
      |> _eqv val_p |-> primR ty 1 expected_v **
      AU1 << _eqv p |-> primR ty 1 v >> @M,∅ (* TODO: masks *)
          << _eqv p |-> primR ty 1 v,
            COMM (_eqv val_p |-> primR ty 1 v -* Q (Vbool false)) >>
      |-- wp_atom' AO__atomic_compare_exchange_n ty
                  (p::succmemord::val_p::failmemord::desired::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & % & Hex & AU)".
    iApply wp_atom_compare_exchange_n_cst. iFrame.
    iAuIntro1.
    iApply (aacc1_aupd_commit with "AU").
  Abort.

  (* An SC compare and exchange *)
  Lemma wp_atom_compare_exchange_cst_suc :
    forall q p expected_p desired_p weak succmemord failmemord Q
      (ty : type)
      expected desired,
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      |> ((* private pre-cond *)
          _eqv expected_p |-> primR ty 1 expected **
           _eqv desired_p |-> primR ty q desired) **
      AU1 << _eqv p |-> primR ty 1 expected >> @M,∅ (* TODO: masks *)
          << (* public post-cond: latest value is desired *)
              _eqv p |-> primR ty 1 desired,
            COMM (_eqv expected_p |-> primR ty 1 expected **
                  _eqv desired_p |-> primR ty q desired -* Q (Vbool true)) >>
      |-- wp_atom' AO__atomic_compare_exchange ty
                  (p::succmemord::expected_p::failmemord::desired_p::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & Pre & AU)".
    iApply wp_atom_compare_exchange_cst. iFrame.
    iAuIntro1.
    iApply (aacc1_aupd_commit with "AU").
  Abort.

  Lemma wp_atom_compare_exchange_cst_fail :
    forall q p expected_p desired_p weak succmemord failmemord Q
      (ty : type)
      v expected desired,
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* we know that the values are different *)
      [| v <> expected |] **
      |> (_eqv expected_p |-> primR ty 1 expected **
           _eqv desired_p |-> primR ty q desired) **
      AU1 << _eqv p |-> primR ty 1 v >> @M,∅ (* TODO: masks *)
          << _eqv p |-> primR ty 1 v,
            COMM (_eqv expected_p |-> primR ty 1 v **
                  _eqv desired_p |-> primR ty q desired -* Q (Vbool false)) >>
      |-- wp_atom' AO__atomic_compare_exchange ty
                  (p::succmemord::expected_p::failmemord::desired_p::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & % & Pre & AU)".
    iApply wp_atom_compare_exchange_cst. iFrame.
    iAuIntro1.
    iApply (aacc1_aupd_commit with "AU").
  Abort.
End cmpxchg_derived.
