(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* This file captures reasoning principles that are necessary when
 * separately verifying #includes
 *)
From iris.proofmode Require Import tactics.
From bedrock.lang.cpp Require Import
     ast logic.pred logic.compilation_unit.

Section with_PROP.
  Context {PROP : sbi}.

  Lemma illater_wandSP : forall (P Q : PROP), |> (P -* Q) |-- (|> P) -* (|> Q).
  Proof.
    iIntros (P Q). iIntros "HPQ HP". iNext. by iApply "HPQ".
  Qed.
  Lemma illater_sepSP : forall (P Q : PROP), |> (P ** Q) -|- (|> P) ** (|> Q).
  Proof.
    iIntros (P Q). iSplit.
    - iIntros "HPQ". by iApply bi.later_sep_1.
    - iIntros "HPQ". iNext. eauto.
  Qed.

  (* note that the meaning of a module must be persistent,
   * if you have non-persistent terms (e.g. ptsto), then you either need
   * to put them inside invariants, or prove that they do not depend on
   * the imports (this would only be a problem if they are initialized via
   * a function call, but I don't think that you can actually do that).
   *)
  Definition module (imports exports : PROP) : PROP :=
    (|> imports) -* exports.

End with_PROP.
