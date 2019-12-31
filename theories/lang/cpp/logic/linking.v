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

Section with_Σ.
Context {Σ:gFunctors}.

Local Notation mpred := (mpred Σ) (only parsing).

Lemma illater_wandSP : forall (P Q : mpred), |> (P -* Q) |-- (|> P) -* (|> Q).
Proof.
  iIntros (P Q). iIntros "HPQ HP". iNext. by iApply "HPQ".
Qed.
Lemma illater_sepSP : forall (P Q : mpred), |> (P ** Q) -|- (|> P) ** (|> Q).
Proof.
  iIntros (P Q). iSplit.
  - iIntros "HPQ". by iApply bi.later_sep_1.
  - iIntros "HPQ". iNext. eauto.
Qed.
Lemma later_empSP : |> (empSP : mpred) -|- empSP.
Proof. iSplit; eauto. Qed.

(* note that the meaning of a module must be persistent,
 * if you have non-persistent terms (e.g. ptsto), then you either need
 * to put them inside invariants, or prove that they do not depend on
 * the imports (this would only be a problem if they are initialized via
 * a function call, but I don't think that you can actually do that).
 *)
Definition module (imports exports : mpred) : mpred :=
  (|> imports) -* exports.

Theorem use_module_prim
: forall (all sub rem : compilation_unit) spec,
    match link sub rem with
    | None => False
    | Some all' => compilation_unit_eq all all' = true
    end ->
    denoteModule (Σ := Σ) sub |-- spec ->
    denoteModule all |-- denoteModule rem ** spec.
Proof. Admitted.


(*
Theorem module_self_link (E : mpred) :
  module E E |-- E.
Proof.
  eapply lob_ind.
  unfold module.
  eapply landAdj.
  reflexivity.
Qed.

Theorem module_link (I1 I2 E1 E2 : mpred) :
  module (E2 ** I1) E1 ** module (E1 ** I2) E2
  |-- module (I1 ** I2) (E1 ** E2).
Proof. Abort.

Lemma lob_link : forall A B : mpred,
    ((|> A) -->> B) //\\ ((|> B) -->> A) |-- A //\\ B.
Proof.
  intros. (*
  eapply sepSPAdj'.
  rewrite <- empSPL.
  eapply sepSPAdj.
  rewrite <- (landtrueR empSP).
  apply landL2.
  rewrite <- wand_curry.
  eapply wandSPAdj.
  eapply lob_ind.
  rewrite illater_sepSP.
  eapply spec_lob.
  eapply wandSPAdj.
  eapply wandSPE.
  reflexivity.
  eapply scME.
  instantiate (1:=|> ((|> B) -* A) ** ((|> A))).
*)

Abort.
*)
    (* |>A ==> B
     * |>B ==> A
     * A //\\ B
     *)
End with_Σ.
