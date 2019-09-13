(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.

From Cpp Require Import
     Ast Sem Util.
From Cpp.Auto Require Import
     Definitions Discharge type.
From Cpp.Syntax Require Import Typing.

Local Ltac t :=
  discharge fail idtac fail fail eauto.

Lemma later_sep : forall P Q R,
    (|> P) ** Q |-- R ->
    P ** Q |-- R.
Proof.
  intros. rewrite <- H. t.
  eapply spec_later_weaken.
Qed.

Lemma appeal_to_universal_arrow_void : forall (P : mpred) Q F F',
    F |-- P ** F' ->
    (Forall res : val, P -* Q) ** F |-- Q ** F'.
Proof.
  intros.
  rewrite sepSPC. rewrite bilforallscR.
  eapply (lforallL (Vint 0))%Z.
  rewrite H.
  t.
  eapply sepSPAdj'. reflexivity.
Qed.

Lemma appeal_to_universal_arrow : forall {T} P Q (F F' : mpred) x,
    F |-- P x ** F' ->
    (Forall res : T, P res -* Q res) ** F |-- Q x ** F'.
Proof.
  intros.
  rewrite sepSPC. rewrite bilforallscR.
  eapply (lforallL x).
  rewrite H.
  t.
  eapply sepSPAdj'. reflexivity.
Qed.

Lemma drop_qualifiers_idem
: forall t, drop_qualifiers (drop_qualifiers t) = drop_qualifiers t.
Proof.
  induction t; simpl; auto.
Qed.

Lemma only_provable_intro_mpred : forall (P : Prop) (Q R : mpred),
    (P -> Q |-- R) -> [| P |] ** Q |-- R.
Proof. eapply provable_intro. Qed.


Lemma cancel_with_later : forall P Q R : mpred,
    Q |-- R ->
    P ** Q |-- (|> P) ** R.
Proof.
  intros. rewrite H; clear H.
  rewrite <- spec_later_weaken.
  reflexivity.
Qed.

Lemma exactly_this_one : forall (P Q : mpred),
    P ** Q |-- P ** ltrue.
Proof. intros. t. Qed.
