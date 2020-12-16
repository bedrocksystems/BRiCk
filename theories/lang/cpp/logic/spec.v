(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.

Require Import stdpp.telescopes.

From iris.proofmode Require Import tactics.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp Require Import pred.

Local Set Universe Polymorphism.

Section with_prop.
  Context {PROP : bi}.

  Record WithEx@{X Z Y} : Type :=
    { we_ex   : tele@{X}
    ; we_post : tele_fun@{X Z Y} we_ex (val * PROP) }.

  Definition WithEx_map (f : val -> PROP -> val * PROP) (we : WithEx)
    : WithEx :=
    {| we_ex := we.(we_ex)
     ; we_post := tele_map (fun '(r,Q) => f r Q) we.(we_post) |}.

  Record WithPrePost@{X Z Y} : Type :=
    { wpp_with : tele@{X}
    ; wpp_pre  : tele_fun@{X Z Y} wpp_with (list val * PROP)
    ; wpp_post : tele_fun@{X Z Y} wpp_with WithEx@{X Z Z} }.

  Fixpoint tbi_exist@{X Z Y} {t : tele@{X}}
    : forall (P : tele_fun@{X Z Y} t PROP), PROP :=
    match t as t0 return ((t0 -t> PROP) → PROP) with
    | [tele] => fun x : PROP => x
    | @TeleS X binder =>
      fun P : (∀ x : X, binder x -t> PROP) => Exists x : X, tbi_exist (P x)
    end.

  Fixpoint tbi_forall@{X Z Y} {t : tele@{X}}
    : forall (P : tele_fun@{X Z Y} t PROP), PROP :=
    match t as t0 return ((t0 -t> PROP) → PROP) with
    | [tele] => fun x : PROP => x
    | @TeleS X binder =>
      fun P : (∀ x : X, binder x -t> PROP) => Forall x : X, tbi_forall (P x)
    end.

  Definition WppD@{X Z Y} (wpp : WithPrePost@{X Z Y}) (params : list val)
             (Q : val -> PROP) : PROP :=
    tbi_exist@{X Z Y} (tele_bind (TT:=wpp.(wpp_with)) (fun args =>
      let P := tele_app wpp.(wpp_pre) args in
      let Q' := tele_app wpp.(wpp_post) args in
      [| params = fst P |] ** snd P **
      tbi_forall@{X Z Y} (tele_map (fun '(result,Q') => Q' -* Q result) Q'.(we_post)))).

End with_prop.
Arguments WithPrePost : clear implicits.
Arguments Build_WithPrePost _ _ _ : clear implicits.
Arguments WithEx : clear implicits.
Arguments Build_WithEx _ _ _ : clear implicits.

Arguments we_ex {PROP} _.
Arguments we_post {PROP} _.
Arguments wpp_with {_} _.
Arguments wpp_pre {_} _.
Arguments wpp_post {_} _.

Global Arguments WppD _ !_ _ _ /.
