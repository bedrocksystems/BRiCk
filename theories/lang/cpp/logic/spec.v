(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.algebra.telescopes.
Require Import bedrock.lang.bi.telescopes.
Require Import bedrock.lang.cpp.semantics.values.
Import ChargeNotation.

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

  (** Analogues of [bi_texist] and [bi_tforall], with extra universe
  polymorphism and a slightly different interface. *)
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

  (** Mnemonic: WppGD stands for "[WithPrePostG]'s denotation" *)
  Definition WppGD@{X Z Y A R} {ARGS RESULT} (wpp : WithPrePostG@{X Z Y A R} ARGS RESULT) (params : ARGS)
             (Q : RESULT -> PROP) : PROP :=
    tbi_exist@{X Z Y} (tele_bind (TT:=wpp.(wpp_with)) (fun args =>
      let P := tele_app wpp.(wpp_pre) args in
      let Q' := tele_app wpp.(wpp_post) args in
      [| params = fst P |] ** snd P **
      tbi_forall@{X Z Y} (tele_map (fun '(result,Q') => Q' -* Q result) Q'.(we_post)))).

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

Section tele_fun_quantifiers.
  Context {PROP : bi} {t : tele}.
  Implicit Types (P : t -t> PROP).
  Implicit Types (R : t -> PROP).

  Lemma tbi_exist_bi_texist P : tbi_exist P -|- ∃.. x, tele_app P x.
  Proof. induction t as [|?? IH]; simpl; first done. f_equiv=>x. by rewrite IH. Qed.
  Lemma bi_texist_tbi_exist R : (∃.. x, R x) -|- tbi_exist (tele_bind R).
  Proof. rewrite tbi_exist_bi_texist. f_equiv=>x. by rewrite tele_app_bind. Qed.
  Lemma tbi_exist_exist P : tbi_exist P -|- Exists x, tele_app P x.
  Proof. by rewrite tbi_exist_bi_texist bi_texist_exist. Qed.

  Lemma tbi_forall_bi_tforall P : tbi_forall P -|- ∀.. x, tele_app P x.
  Proof. induction t as [|?? IH]; simpl; first done. f_equiv=>x. by rewrite IH. Qed.
  Lemma bi_tforall_tbi_forall R : (∀.. x, R x) -|- tbi_forall (tele_bind R).
  Proof. rewrite tbi_forall_bi_tforall. f_equiv=>x. by rewrite tele_app_bind. Qed.
  Lemma tbi_forall_forall P : tbi_forall P -|- Forall x, tele_app P x.
  Proof. by rewrite tbi_forall_bi_tforall bi_tforall_forall. Qed.

  #[global] Instance tbi_exist_ne : NonExpansive (@tbi_exist PROP t).
  Proof. intros n P Q ?. rewrite !tbi_exist_exist. solve_proper. Qed.
  #[global] Instance tbi_exist_proper : Proper (equiv ==> equiv) (@tbi_exist PROP t).
  Proof.
    apply ne_proper.
    (** TODO: Typeclass resolution here takes a long time to find
        [tbi_exist_ne] because it first tries [contractive_ne]. Can
        similarly slow searches arise downstream? *)
    apply tbi_exist_ne.
  Qed.

  #[global] Instance tbi_forall_ne : NonExpansive (@tbi_forall PROP t).
  Proof. intros n P Q ?. rewrite !tbi_forall_forall. solve_proper. Qed.
  #[global] Instance tbi_forall_proper : Proper (equiv ==> equiv) (@tbi_forall PROP t).
  Proof. apply ne_proper, tbi_forall_ne. Qed.
End tele_fun_quantifiers.

Section wpp_ofe.
  Context {PROP : bi} {ARGS RESULT : Type}.
  Notation WPP := (WithPrePostG PROP ARGS RESULT) (only parsing).

  Instance wpp_equiv : Equiv WPP :=
    fun wpp1 wpp2 => forall x Q, WppGD wpp1 x Q ≡ WppGD wpp2 x Q.
  Instance wpp_dist : Dist WPP :=
    fun n wpp1 wpp2 => forall x Q, WppGD wpp1 x Q ≡{n}≡ WppGD wpp2 x Q.

  Lemma wpp_ofe_mixin : OfeMixin WPP.
  Proof.
    exact: (iso_ofe_mixin (A:=ARGS -d> (RESULT -> PROP) -d> PROP) WppGD).
  Qed.
  Canonical Structure WithPrePostGO := OfeT WPP wpp_ofe_mixin.
End wpp_ofe.
Arguments WithPrePostGO : clear implicits.
Notation WithPrePostO PROP := (WithPrePostGO PROP (list val) val).
