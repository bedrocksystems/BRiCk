(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Lists.List.

Require Import stdpp.telescopes.

From iris.proofmode Require Import tactics.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp Require Import pred.

Local Set Universe Polymorphism.

Section with_prop.
  Context {PROP : bi}.

  Record WithExG@{X Z Y R} {RESULT : Type@{R}} : Type :=
    { we_ex   : tele@{X}
    ; we_post : tele_fun@{X Z Y} we_ex (RESULT * PROP) }.
  Global Arguments WithExG : clear implicits.

  Definition WithExG_map@{X Z Y T U} {T : Type@{T}} {U : Type@{U}} (f : T -> PROP -> U * PROP)
    (we : WithExG@{X Z Y T} T) : WithExG@{X Z Y U} U :=
    {| we_ex := we.(we_ex)
     ; we_post := tele_map (fun '(r,Q) => f r Q) we.(we_post) |}.

  Record WithPrePostG@{X Z Y A R} {ARGS : Type@{A}} {RESULT : Type@{R}} :=
    { wpp_with : tele@{X}
    ; wpp_pre  : tele_fun@{X Z Y} wpp_with (ARGS * PROP)
    ; wpp_post : tele_fun@{X Z Y} wpp_with (WithExG@{X Z _ _} RESULT)}.
  Global Arguments WithPrePostG : clear implicits.

  (** Mnemonic: WppGD stands for "[WithPrePostG]'s denotation" *)
  Definition WppGD@{X Z Y A R} {ARGS RESULT} (wpp : WithPrePostG@{X Z Y A R} ARGS RESULT) (params : ARGS)
             (Q : RESULT -> PROP) : PROP :=
    bi_texist (fun args =>
      let P := tele_app wpp.(wpp_pre) args in
      let Q' := tele_app wpp.(wpp_post) args in
      [| params = fst P |] ** snd P **
      bi_tforall (tele_app@{_ X _} (tele_map (fun '(result,Q') => Q' -* Q result) Q'.(we_post)))).

  (* Aliases specialized to [val]. We use definitions to control the universe
  arguments. *)
  Definition WithEx@{X Z Y} := WithExG@{X Z Y _} val.
  Definition WithPrePost@{X Z Y} := WithPrePostG@{X Z Y _ _} (list val) val.
  Definition WppD@{X Z Y} := (WppGD@{X Z Y _ _} (ARGS := list val) (RESULT := val)).
  Definition WithEx_map@{X Z Y} := WithExG_map@{X Z Y _ _} (T := val) (U := val).
End with_prop.

Arguments WithPrePostG : clear implicits.
Arguments WithPrePost : clear implicits.
Arguments Build_WithPrePostG _ _ _ : clear implicits.
Arguments WithExG : clear implicits.
Arguments WithEx : clear implicits.
Arguments Build_WithExG _ _ _ : clear implicits.

Arguments we_ex {PROP RESULT} _ : assert.
Arguments we_post {PROP RESULT} _ : assert.
Arguments wpp_with {PROP ARGS RESULT} _: assert.
Arguments wpp_pre {PROP ARGS RESULT} _: assert.
Arguments wpp_post {PROP ARGS RESULT} _: assert.

Global Arguments WppGD {PROP ARGS RESULT} !wpp _ _ / : assert.
Global Arguments WppD {PROP} !wpp _ _ / : assert.
