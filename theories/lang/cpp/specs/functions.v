(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.bi.ChargeCompat.
Require Import bedrock.lang.bi.telescopes.
Require Import bedrock.lang.cpp.logic.entailsN.
Require Import bedrock.lang.bi.errors.
Require Import iris.proofmode.proofmode.	(** Early to get the right [ident] *)
Require Import bedrock.lang.cpp.logic.
Require Export bedrock.lang.cpp.specs.with_pre_post.
Require Import bedrock.lang.cpp.heap_notations.

#[local] Set Universe Polymorphism.
#[local] Set Printing Universes.
#[local] Set Printing Coercions.

Arguments ERROR {_ _} _%bs.
Arguments UNSUPPORTED {_ _} _%bs.

(** * Wrappers to build [function_spec] from a [WithPrePost] *)

(* A specification for a function  *)
Definition SFunction@{X Z Y} `{Σ : cpp_logic} {cc : calling_conv}
    (ret : type) (targs : list type) (PQ : WithPrePost@{X Z Y} mpredI)
    : function_spec :=
  {| fs_cc        := cc
   ; fs_return    := ret
   ; fs_arguments := targs
   ; fs_spec      := WppD PQ |}.

(* A specification for a constructor *)
Definition SConstructor@{X Z Y} `{Σ : cpp_logic, resolve : genv} {cc : calling_conv}
    (class : globname) (targs : list type) (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
    : function_spec :=
  let this_type := Qmut (Tnamed class) in
  let map_pre this '(args, P) :=
    (Vptr this :: args,
     this |-> tblockR (Tnamed class) 1 ** P)
  in
  SFunction (cc:=cc) (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
    {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
     ; wpp_pre this := tele_map (map_pre this) (PQ this).(wpp_pre)
     ; wpp_post this := (PQ this).(wpp_post)
     |}.

(* A specification for a destructor *)
Definition SDestructor@{X Z Y} `{Σ : cpp_logic, resolve : genv} {cc : calling_conv}
    (class : globname) (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
    : function_spec :=
  let this_type := Qmut (Tnamed class) in
  let map_pre this '(args, P) := (Vptr this :: args, P) in
  let map_post (this : ptr) '{| we_ex := pwiths ; we_post := Q|} :=
    {| we_ex := pwiths
     ; we_post := tele_map (fun '(result, Q) =>
      (result, this |-> tblockR (Tnamed class) 1 ** Q)) Q
     |}
  in
  (** ^ NOTE the size of an object might be different in the presence
      of virtual base classes. *)
  SFunction@{X Z Y} (cc:=cc) (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
    {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
     ; wpp_pre this := tele_map (map_pre this) (PQ this).(wpp_pre)
     ; wpp_post this := tele_map (map_post this) (PQ this).(wpp_post)
    |}.

(* A specification for a method *)
(** Sometimes, especially after a virtual function resolution,
 *  [this] pointer needs to be adjusted before a call. *)
#[local] Definition SMethodOptCast_wpp@{X Z Y} `{Σ : cpp_logic}
    (base_to_derived : option offset) (wpp : ptr -> WithPrePost@{X Z Y} mpredI)
    : WithPrePost@{X Z Y} mpredI :=
  let map_pre this pair :=
      (Vptr (if base_to_derived is Some o then (this ., o ) else this) :: pair.1, pair.2) in
  {| wpp_with := TeleS (fun this : ptr => (wpp this).(wpp_with))
   ; wpp_pre this := tele_map (map_pre this) (wpp this).(wpp_pre)
   ; wpp_post this := (wpp this).(wpp_post)
   |}.
#[local] Definition SMethodOptCast@{X Z Y} `{Σ : cpp_logic} {cc : calling_conv}
    (class : globname) (base_to_derived : option offset) (qual : type_qualifiers)
    (ret : type) (targs : list type)
    (PQ : ptr -> WithPrePost@{X Z Y} mpredI) : function_spec :=
  let class_type := Tnamed class in
  let this_type := Tqualified qual class_type in
  SFunction@{X Z Y} (cc:=cc) ret (Qconst (Tpointer this_type) :: targs)
    (SMethodOptCast_wpp base_to_derived PQ).
Definition SMethodCast@{X Z Y} `{Σ : cpp_logic} {cc : calling_conv}
    (class : globname) (base_to_derived : offset) (qual : type_qualifiers)
    (ret : type) (targs : list type)
    (PQ : ptr -> WithPrePost@{X Z Y} mpredI) : function_spec :=
  SMethodOptCast (cc:=cc) class (Some base_to_derived) qual ret targs PQ.
Definition SMethod@{X Z Y} `{Σ : cpp_logic} {cc : calling_conv}
    (class : globname) (qual : type_qualifiers) (ret : type) (targs : list type)
    (PQ : ptr -> WithPrePost@{X Z Y} mpredI) : function_spec :=
  SMethodOptCast (cc:=cc) class None qual ret targs PQ.

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

  #[local] Notation _base := (o_base resolve).
  #[local] Notation _derived := (o_derived resolve).

  (** The following monotonicity lemmas are (i) stated so that they
      don't force a pair of related WPPs to share universes and (ii)
      proved so that they don't constrain the WPP universes [Y1], [Y2]
      from above. The TC instances are strictly less useful, as they
      necessarily give up on both (i) and (ii). *)
  Section SFunction.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (ret : type) (targs : list type).

    Lemma SFunction_mono@{X1 X2 Z1 Z2 Y1 Y2} wpp1 wpp2 :
      wpp_entails wpp2 wpp1 ->
      fs_entails
        (SFunction@{X1 Z1 Y1} (cc:=cc) ret targs wpp1)
        (SFunction@{X2 Z2 Y2} (cc:=cc) ret targs wpp2).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (vs K) "wpp". by iApply Hwpp.
    Qed.

    #[global] Instance: Params (@SFunction) 5 := {}.
    #[global] Instance SFunction_ne : NonExpansive (SFunction (cc:=cc) ret targs).
    Proof.
      intros n wpp1 wpp2 Hwpp. split; by rewrite/type_of_spec/=.
    Qed.

    #[global] Instance SFunction_proper :
      Proper (equiv ==> equiv) (SFunction (cc:=cc) ret targs).
    Proof. exact: ne_proper. Qed.

    #[global] Instance SFunction_mono'@{X Z Y} :
      Proper (flip wpp_entails ==> fs_entails) (SFunction@{X Z Y} (cc:=cc) ret targs).
    Proof. repeat intro. by apply SFunction_mono. Qed.

    #[global] Instance SFunction_flip_mono'@{X Z Y} :
      Proper (wpp_entails ==> flip fs_entails)
        (SFunction@{X Z Y} (cc:=cc) ret targs).
    Proof. solve_proper. Qed.
  End SFunction.

  Section SMethod.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (class : globname) (qual : type_qualifiers).
    Context (ret : type) (targs : list type).

    (** We could derive [SMethod_mono] from the following
        [SMethod_wpp_monoN]. We retain this proof because it's easier
        to understand and it goes through without [BiEntailsN]. *)
    #[local] Lemma SMethodOptCast_mono@{X1 X2 Z1 Z2 Y1 Y2} cast wpp1 wpp2 :
      (∀ this, wpp_entails (wpp2 this) (wpp1 this)) ->
      fs_entails
        (SMethodOptCast@{X1 Z1 Y1} (cc:=cc) class cast qual ret targs wpp1)
        (SMethodOptCast@{X2 Z2 Y2} (cc:=cc) class cast qual ret targs wpp2).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (vs K) "wpp".
      (** To apply [Hwpp], we have to deconstruct the WPP we've got,
          stripping off the extra "this" argument. *)
      iDestruct "wpp" as (this) "wpp". rewrite {1}tbi_exist_exist.
      iDestruct "wpp" as (xs) "wpp". rewrite tele_app_bind tele_map_app.
      destruct (tele_app _ xs) as [args P] eqn:Hargs. simpl.
      iDestruct "wpp" as "(-> & pre & post)".
      iDestruct (Hwpp this args K with "[pre post]") as "wpp".
      { rewrite /WppD/WppGD. rewrite tbi_exist_exist.
        iExists xs. rewrite tele_app_bind Hargs/=. by iFrame "pre post". }
      iExists this. rewrite tbi_exist_exist. rewrite/WppD/WppGD tbi_exist_exist.
      iDestruct "wpp" as (ys) "wpp". rewrite tele_app_bind.
      iDestruct "wpp" as "(-> & pre & post)".
      iExists ys. rewrite tele_app_bind tele_map_app. simpl. by iFrame "pre post".
    Qed.

    Lemma SMethodCast_mono@{X1 X2 Z1 Z2 Y1 Y2} cast wpp1 wpp2 :
      (∀ this, wpp_entails (wpp2 this) (wpp1 this)) ->
      fs_entails
        (SMethodOptCast@{X1 Z1 Y1} (cc:=cc) class cast qual ret targs wpp1)
        (SMethodOptCast@{X2 Z2 Y2} (cc:=cc) class cast qual ret targs wpp2).
    Proof. exact: SMethodOptCast_mono. Qed.

    Lemma SMethod_mono@{X1 X2 Z1 Z2 Y1 Y2} wpp1 wpp2 :
      (∀ this, wpp_entails (wpp2 this) (wpp1 this)) ->
      fs_entails
        (SMethod@{X1 Z1 Y1} (cc:=cc) class qual ret targs wpp1)
        (SMethod@{X2 Z2 Y2} (cc:=cc) class qual ret targs wpp2).
    Proof. exact: SMethodOptCast_mono. Qed.

    #[local] Lemma SMethodOptCast_wpp_monoN@{X1 X2 Z1 Z2 Y1 Y2}
        c wpp1 wpp2 vs K n :
      (∀ this, wpp_entailsN n (wpp1 this) (wpp2 this)) ->
      WppD@{X1 Z1 Y1} (SMethodOptCast_wpp c wpp1) vs K ⊢{n}
      WppD@{X2 Z2 Y2} (SMethodOptCast_wpp c wpp2) vs K.
    Proof.
      move=>Hwpp /=. f_equiv=>this.
      rewrite !tbi_exist_exist. set M1 := tele_app _. set M2 := tele_app _.
      apply exist_elimN=>x1. rewrite /M1 {M1} tele_app_bind tele_map_app.
      destruct (tele_app _ x1) as [vs1 P1] eqn:Hvs1; simpl.
      apply wand_elimN_l', only_provable_elimN'; intros ->;
        apply wand_introN_r; rewrite left_id.
      move: {Hwpp} (Hwpp this vs1 K). rewrite/WppD/WppGD.
      rewrite !tbi_exist_exist. set F1 := tele_app _. set F2 := tele_app _.
      move=>HF. trans (Exists x, F1 x).
      { apply (exist_introN' _ _ x1). rewrite/F1 tele_app_bind Hvs1 /=.
        rewrite -{1}[P1](left_id emp%I bi_sep) -assoc. f_equiv.
        exact: only_provable_introN. }
      rewrite {F1}HF. f_equiv=>x2. rewrite /F2 {F2} tele_app_bind.
      rewrite /M2 {M2} tele_app_bind tele_map_app. simpl. f_equiv.
      apply only_provable_elimN'=>->. exact: only_provable_introN.
    Qed.

    #[local] Lemma SMethodOptCast_ne@{X Y Z} cast wpp1 wpp2 n :
      (∀ this, wpp_dist n (wpp1 this) (wpp2 this)) ->
      SMethodOptCast@{X Y Z} (cc:=cc) class cast qual ret targs wpp1 ≡{n}≡
      SMethodOptCast@{X Y Z} (cc:=cc) class cast qual ret targs wpp2.
    Proof.
      setoid_rewrite wpp_dist_entailsN=>Hwpp.
      rewrite/SMethodOptCast. f_equiv=>vs K /=. apply dist_entailsN.
      split; apply SMethodOptCast_wpp_monoN=>this; by destruct (Hwpp this).
    Qed.

    Lemma SMethodCast_ne@{X Y Z} cast wpp1 wpp2 n :
      (∀ this, wpp_dist n (wpp1 this) (wpp2 this)) ->
      SMethodCast@{X Y Z} (cc:=cc) class cast qual ret targs wpp1 ≡{n}≡
      SMethodCast@{X Y Z} (cc:=cc) class cast qual ret targs wpp2.
    Proof. exact: SMethodOptCast_ne. Qed.

    Lemma SMethod_ne@{X Y Z} wpp1 wpp2 n :
      (∀ this, wpp_dist n (wpp1 this) (wpp2 this)) ->
      SMethod@{X Y Z} (cc:=cc) class qual ret targs wpp1 ≡{n}≡
      SMethod@{X Y Z} (cc:=cc) class qual ret targs wpp2.
    Proof. exact: SMethodOptCast_ne. Qed.

    #[local] Lemma SMethodOptCast_proper@{X1 X2 Z1 Z2 Y1 Y2} cast wpp1 wpp2 :
      (∀ this, wpp_equiv (wpp1 this) (wpp2 this)) ->
      SMethodOptCast@{X1 Z1 Y1} (cc:=cc) class cast qual ret targs wpp1 ≡
      SMethodOptCast@{X2 Z2 Y2} (cc:=cc) class cast qual ret targs wpp2.
    Proof.
      setoid_rewrite wpp_equiv_spec=>Hwpp. apply function_spec_equiv_split.
      split; apply SMethodCast_mono=>this; by destruct (Hwpp this).
    Qed.
    Lemma SMethodCast_proper@{X1 X2 Z1 Z2 Y1 Y2} cast wpp1 wpp2 :
      (∀ this, wpp_equiv (wpp1 this) (wpp2 this)) ->
      SMethodCast@{X1 Z1 Y1} (cc:=cc) class cast qual ret targs wpp1 ≡
      SMethodCast@{X2 Z2 Y2} (cc:=cc) class cast qual ret targs wpp2.
    Proof. exact: SMethodOptCast_proper. Qed.
    Lemma SMethod_proper@{X1 X2 Z1 Z2 Y1 Y2} wpp1 wpp2 :
      (∀ this, wpp_equiv (wpp1 this) (wpp2 this)) ->
      SMethod@{X1 Z1 Y1} (cc:=cc) class qual ret targs wpp1 ≡
      SMethod@{X2 Z2 Y2} (cc:=cc) class qual ret targs wpp2.
    Proof. exact: SMethodOptCast_proper. Qed.

    #[global] Instance: Params (@SMethodCast) 8 := {}.
    #[global] Instance: Params (@SMethod) 7 := {}.
    #[global] Instance SMethodCast_ne' cast n :
      Proper (dist (A:=ptr -d> WithPrePostO mpredI) n ==> dist n)
        (SMethodCast (cc:=cc) class cast qual ret targs).
    Proof. repeat intro. by apply SMethodCast_ne. Qed.
    #[global] Instance SMethod_ne' n :
      Proper (dist (A:=ptr -d> WithPrePostO mpredI) n ==> dist n)
        (SMethod (cc:=cc) class qual ret targs).
    Proof. repeat intro. by apply SMethod_ne. Qed.

    #[global] Instance SMethodCast_proper' cast :
      Proper (equiv (A:=ptr -d> WithPrePostO mpredI) ==> equiv)
        (SMethodCast (cc:=cc) class cast qual ret targs).
    Proof. exact: ne_proper. Qed.
    #[global] Instance SMethod_proper' :
      Proper (equiv (A:=ptr -d> WithPrePostO mpredI) ==> equiv)
        (SMethod (cc:=cc) class qual ret targs).
    Proof. exact: ne_proper. Qed.

    #[global] Instance SMethodCast_mono'@{X Z Y} cast :
      Proper (pointwise_relation _ (flip wpp_entails) ==> fs_entails)
        (SMethodCast@{X Z Y} (cc:=cc) class cast qual ret targs).
    Proof. repeat intro. by apply SMethodCast_mono. Qed.
    #[global] Instance SMethod_mono'@{X Z Y} :
      Proper (pointwise_relation _ (flip wpp_entails) ==> fs_entails)
        (SMethod@{X Z Y} (cc:=cc) class qual ret targs).
    Proof. repeat intro. by apply SMethod_mono. Qed.

    #[global] Instance SMethodCast_flip_mono'@{X Z Y} cast :
      Proper (pointwise_relation _ wpp_entails ==> flip fs_entails)
        (SMethodCast@{X Z Y} (cc:=cc) class cast qual ret targs).
    Proof. repeat intro. by apply SMethodCast_mono. Qed.
    #[global] Instance SMethod_flip_mono'@{X Z Y} :
      Proper (pointwise_relation _ wpp_entails ==> flip fs_entails)
        (SMethod@{X Z Y} (cc:=cc) class qual ret targs).
    Proof. repeat intro. by apply SMethod_mono. Qed.
  End SMethod.

End with_cpp.
