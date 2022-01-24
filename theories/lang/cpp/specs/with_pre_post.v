(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.algebra.telescopes.
Require Import bedrock.lang.bi.telescopes.
Require Import bedrock.lang.cpp.semantics.values.
Require Import bedrock.lang.cpp.logic.entailsN.
Import ChargeNotation.

#[local] Set Universe Polymorphism.
#[local] Set Printing Universes.
#[local] Set Printing Coercions.

(** The universes in [WithPrePostG], [WithExG] are best seen with
    [Unset Printing Notations] to expose [tele_fun]'s universes:

    - X: The telescopes [wpp_with], [we_ex], i.e., the domains of the
      telescopic functions [wpp_pre], [wpp_post], [we_post].

    - Z: The codomains of the telescopic functions

    - Y: The telescopic functions themselves

    - A: [wpp_pre] argument type

    - R: [wpp_post], [we_ex] result type *)
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

Module Export wpp_ofe.
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
  Canonical Structure WithPrePostGO := Ofe WPP wpp_ofe_mixin.
End wpp_ofe.
End wpp_ofe.
Arguments WithPrePostGO : clear implicits.
Notation WithPrePostO PROP := (WithPrePostGO PROP (list val) val).

(** Universe polymorphic relations between WPPs. *)
Definition wppg_relation@{X1 X2 Z1 Z2 Y1 Y2 A R} {PROP : bi} (R : relation PROP)
    {ARGS : Type@{A}} {RESULT : Type@{R}}
    (wpp1 : WithPrePostG@{X1 Z1 Y1 A R} PROP ARGS RESULT)
    (wpp2 : WithPrePostG@{X2 Z2 Y2 A R} PROP ARGS RESULT) : Prop :=
  (** We use a single [K] rather than pointwise equal [K1], [K2] for
      compatibility with [fs_entails], [fs_impl]. *)
  forall xs K, R (WppGD wpp1 xs K) (WppGD wpp2 xs K).
#[global] Instance: Params (@wppg_relation) 4 := {}.

Notation wppg_entailsN n := (wppg_relation (entailsN n)) (only parsing).
Notation wppg_entails := (wppg_relation bi_entails) (only parsing).
Notation wppg_dist n := (wppg_relation (dist n)) (only parsing).
Notation wppg_equiv := (wppg_relation equiv) (only parsing).

Definition wpp_relation@{X1 X2 Z1 Z2 Y1 Y2} {PROP : bi} (R : relation PROP)
    (wpp1 : WithPrePost@{X1 Z1 Y1} PROP)
    (wpp2 : WithPrePost@{X2 Z2 Y2} PROP) : Prop :=
  (** Can generate nicer goals compared to [:= wppg_entails ...]. *)
  forall xs K, R (WppD wpp1 xs K) (WppD wpp2 xs K).
#[global] Instance: Params (@wpp_relation) 2 := {}.

Notation wpp_entailsN n := (wpp_relation (entailsN n)) (only parsing).
Notation wpp_entails := (wpp_relation bi_entails) (only parsing).
Notation wpp_dist n := (wpp_relation (dist n)) (only parsing).
Notation wpp_equiv := (wpp_relation equiv) (only parsing).

Section wpp_relations.
  Universe X1 X2 Z1 Z2 Y1 Y2.
  Context `{!BiEntailsN PROP}.

  Lemma wppg_equiv_spec@{A R} {ARGS : Type@{A}} {RESULT : Type@{R}} wpp1 wpp2 :
    @wppg_relation@{X1 X2 Z1 Z2 Y1 Y2 A R} PROP (≡) ARGS RESULT wpp1 wpp2 <->
    @wppg_relation@{X1 X2 Z1 Z2 Y1 Y2 A R} PROP (⊢) ARGS RESULT wpp1 wpp2 /\
    @wppg_relation@{X2 X1 Z2 Z1 Y2 Y1 A R} PROP (⊢) ARGS RESULT wpp2 wpp1.
  Proof.
    split.
    - intros Hwpp. by split=>vs K; rewrite (Hwpp vs K).
    - intros [] vs K. by split'.
  Qed.

  Lemma wpp_equiv_spec wpp1 wpp2 :
    @wpp_relation@{X1 X2 Z1 Z2 Y1 Y2} PROP (≡) wpp1 wpp2 <->
    @wpp_relation@{X1 X2 Z1 Z2 Y1 Y2} PROP (⊢) wpp1 wpp2 /\
    @wpp_relation@{X2 X1 Z2 Z1 Y2 Y1} PROP (⊢) wpp2 wpp1.
  Proof. apply wppg_equiv_spec. Qed.

  Lemma wppg_equiv_dist@{A R} {ARGS : Type@{A}} {RESULT : Type@{R}} wpp1 wpp2 :
    @wppg_relation@{X1 X2 Z1 Z2 Y1 Y2 A R} PROP (≡) ARGS RESULT wpp1 wpp2 <->
    ∀ n, @wppg_relation@{X1 X2 Z1 Z2 Y1 Y2 A R} PROP (dist n) ARGS RESULT wpp1 wpp2.
  Proof.
    split.
    - intros Hwpp n vs K. apply equiv_dist, Hwpp.
    - intros Hwpp vs K. apply equiv_dist=>n. apply Hwpp.
  Qed.

  Lemma wpp_equiv_dist wpp1 wpp2 :
    @wpp_relation@{X1 X2 Z1 Z2 Y1 Y2} PROP (≡) wpp1 wpp2 <->
    ∀ n, @wpp_relation@{X1 X2 Z1 Z2 Y1 Y2} PROP (dist n) wpp1 wpp2.
  Proof. apply wppg_equiv_dist. Qed.

  Notation entailsN := (@entailsN PROP).

  Lemma wppg_dist_entailsN@{A R} {ARGS : Type@{A}} {RESULT : Type@{R}} wpp1 wpp2 n :
    @wppg_relation@{X1 X2 Z1 Z2 Y1 Y2 A R} _ (dist n) ARGS RESULT wpp1 wpp2 <->
    @wppg_relation@{X1 X2 Z1 Z2 Y1 Y2 A R} _ (entailsN n) ARGS RESULT wpp1 wpp2 /\
    @wppg_relation@{X2 X1 Z2 Z1 Y2 Y1 A R} _ (entailsN n) ARGS RESULT wpp2 wpp1.
  Proof.
    split.
    - intros Hwpp. by split=>vs K; apply dist_entailsN; rewrite (Hwpp vs K).
    - intros [] vs K. by apply dist_entailsN.
  Qed.

  Lemma wpp_dist_entailsN wpp1 wpp2 n :
    @wpp_relation@{X1 X2 Z1 Z2 Y1 Y2} _ (dist n) wpp1 wpp2 <->
    @wpp_relation@{X1 X2 Z1 Z2 Y1 Y2} _ (entailsN n) wpp1 wpp2 /\
    @wpp_relation@{X2 X1 Z2 Z1 Y2 Y1} _ (entailsN n) wpp2 wpp1.
  Proof. apply wppg_dist_entailsN. Qed.

End wpp_relations.

(** Combinators for building [WithPrePostG]s *)
Section with_AR.
  Context {PROP : bi}.
  #[local] Set Universe Polymorphism.
  #[universes(polymorphic=yes)] Universes X Z Y A R.
  Context {A : Type@{A}} {R : Type@{R}}.

  #[local] Notation WPP := (WithPrePostG@{X Z Y A R} PROP).

  (** [add_with] adds ghost variables scoped over the pre-
      and post-conditions.
   *)
  Definition add_with {t : tele} (wpp : t -t> WPP A R) : WPP A R.
    refine
      {| wpp_with := tele_append t (tele_map wpp_with wpp)
       ; wpp_pre  := _
       ; wpp_post := _
       |}.
    { refine ((fix go (t : tele)  :=
                 match t as t
                       return forall (wpp : t -t> WPP A R),
                     tele_append t (tele_map wpp_with wpp) -t> A * PROP
                 with
                 | TeleO => fun wpp => wpp.(wpp_pre)
                 | TeleS rst => fun wpp x => go (rst x) (wpp x)
                 end) t wpp).
    }
    { refine ((fix go (t : tele)  :=
                 match t as t
                       return forall (wpp : t -t> WPP A R),
                     tele_append t (tele_map wpp_with wpp) -t> _
                 with
                 | TeleO => fun wpp => wpp.(wpp_post)
                 | TeleS rst => fun wpp x => go (rst x) (wpp x)
                 end) t wpp).
    }
  Defined.

  (** [add_pre P wpp] adds [P] as a pre-condition to [wpp] *)
  Definition add_pre (P : PROP) (wpp : WPP A R) : WPP A R :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := tele_map (fun '(args,X) => (args, P ** X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
     |}.

  (** [add_require P wpp] adds [P] as a pure pre-condition to [wpp] *)
  Definition add_require (P : Prop) (wpp : WPP A R) : WPP A R :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre := tele_map (fun '(args,X) => (args, [| P |] ** X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
     |}.

  (** [add_require P wpp] adds [P] as a persistent pre-condition to [wpp] *)
  Definition add_persist (P : PROP) (wpp : WPP A R) : WPP A R :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre := tele_map (fun '(args,X) => (args, □ P ** X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
     |}.

  (** [add_post P wpp] adds [P] as a post-condition to [wpp] *)
  Definition add_post (P : PROP) (wpp : WPP A R) : WPP A R :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := wpp.(wpp_pre)
     ; wpp_post := tele_map (WithExG_map (fun r Q => (r,P ** Q))) wpp.(wpp_post)
     |}.

  (** [add_prepost P wpp] adds [P] as a pre- and post-condition to [wpp] *)
  Definition add_prepost (P : PROP) (wpp : WPP A R) : WPP A R :=
    add_pre P (add_post P wpp).

  (** [add_arg x v wpp] adds an argument (named [x]) with value [v] to
      the beginning of [wpp].

      NOTE this requires that the arguments are a [list]
   *)
  Definition add_arg (s : names.ident) (v : A)
             (wpp : WPP (list A) R) : WPP (list A) R :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := tele_map (fun '(args,X) => (v :: args, X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
    |}.

  (** [post_ret Q] is a specification where the post-condition is.

      NOTE this requires that the arguments are a [list], but this could be
           something with a unit.
   *)
  Definition post_ret {t : tele} (Q : t -t> R * PROP) : WPP (list A) R :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, emp%I)
     ; wpp_post := {| we_ex := t
                    ; we_post := Q |} |}.

  (** [post_void void Q] is a specialization of [post_ret] where the return
      value does not depend on any quantifiers introduced in [Q].

      NOTE this requires that the arguments are a [list], but this could be
           something with a unit.
   *)
  Definition post_void (void : R) (t : tele) (Q : t -t> PROP) : WPP (list A) R :=
    post_ret (t:=t) (tele_map (fun Q => (void, Q)) Q).

End with_AR.

