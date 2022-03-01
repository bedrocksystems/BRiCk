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
Require Import bedrock.lang.cpp.specs.cpp_specs.
Require Import bedrock.lang.cpp.heap_notations.

#[local] Set Printing Universes.
#[local] Set Printing Coercions.

Arguments ERROR {_ _} _%bs.
Arguments UNSUPPORTED {_ _} _%bs.

(** * Wrappers to build [function_spec] from a [WithPrePost] *)

#[local] Notation SPEC := (WpSpec_cpp) (only parsing).

(* A specification for a function  *)
Definition SFunction `{Σ : cpp_logic} {cc : calling_conv}
    (ret : type) (targs : list type) (PQ : SPEC)
    : function_spec :=
  {| fs_cc        := cc
   ; fs_return    := ret
   ; fs_arguments := targs
   ; fs_spec      := wp_specD PQ |}.

(* A specification for a constructor *)
Definition SConstructor `{Σ : cpp_logic, resolve : genv} {cc : calling_conv}
    (class : globname) (targs : list type) (PQ : ptr -> SPEC)
    : function_spec :=
  let this_type := Qmut (Tnamed class) in
  SFunction (cc:=cc) (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
            (\arg{this} "this" (Vptr this)
             \pre this |-> tblockR (Tnamed class) 1
             \exact PQ this).

(* A specification for a destructor *)
Definition SDestructor `{Σ : cpp_logic, resolve : genv} {cc : calling_conv}
    (class : globname) (PQ : ptr -> SPEC)
    : function_spec :=
  let this_type := Qmut (Tnamed class) in
  (** ^ NOTE the size of an object might be different in the presence
      of virtual base classes. *)
  SFunction (cc:=cc) (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
           (\arg{this} "this" (Vptr this)
            \exact add_post (_at this (tblockR (Tnamed class) 1)) (PQ this)).

(* A specification for a method *)
(** Sometimes, especially after a virtual function resolution,
 *  [this] pointer needs to be adjusted before a call. *)
#[local] Definition SMethodOptCast_wpp`{Σ : cpp_logic}
    (base_to_derived : option offset) (wpp : ptr -> SPEC)
  : SPEC :=
  \arg{this} "this"
   (Vptr (if base_to_derived is Some o then (this ., o ) else this))
  \exact (wpp this).
#[local] Definition SMethodOptCast `{Σ : cpp_logic} {cc : calling_conv}
    (class : globname) (base_to_derived : option offset) (qual : type_qualifiers)
    (ret : type) (targs : list type)
    (PQ : ptr -> SPEC) : function_spec :=
  let class_type := Tnamed class in
  let this_type := Tqualified qual class_type in
  SFunction (cc:=cc) ret (Qconst (Tpointer this_type) :: targs)
    (SMethodOptCast_wpp base_to_derived PQ).
Definition SMethodCast `{Σ : cpp_logic} {cc : calling_conv}
    (class : globname) (base_to_derived : offset) (qual : type_qualifiers)
    (ret : type) (targs : list type)
    (PQ : ptr -> SPEC) : function_spec :=
  SMethodOptCast (cc:=cc) class (Some base_to_derived) qual ret targs PQ.
Definition SMethod `{Σ : cpp_logic} {cc : calling_conv}
    (class : globname) (qual : type_qualifiers) (ret : type) (targs : list type)
    (PQ : ptr -> SPEC) : function_spec :=
  SMethodOptCast (cc:=cc) class None qual ret targs PQ.

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

  #[local] Notation _base := (o_base resolve).
  #[local] Notation _derived := (o_derived resolve).

  (** The following monotonicity lemmas are (i) stated so that they
      don't force a pair of related SPECs to share universes and (ii)
      proved so that they don't constrain the  universes [Y1], [Y2]
      from above. The TC instances are strictly less useful, as they
      necessarily give up on both (i) and (ii). *)
  Section SFunction.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (ret : type) (targs : list type).

    Lemma SFunction_mono wpp1 wpp2 :
      wpspec_entails wpp2 wpp1 ->
      fs_entails
        (SFunction (cc:=cc) ret targs wpp1)
        (SFunction (cc:=cc) ret targs wpp2).
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

    #[global] Instance SFunction_mono' :
      Proper (flip wpspec_entails ==> fs_entails) (SFunction (cc:=cc) ret targs).
    Proof. repeat intro. by apply SFunction_mono. Qed.

    #[global] Instance SFunction_flip_mono' :
      Proper (wpspec_entails ==> flip fs_entails)
        (SFunction (cc:=cc) ret targs).
    Proof. solve_proper. Qed.
  End SFunction.

  Section SMethod.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (class : globname) (qual : type_qualifiers).
    Context (ret : type) (targs : list type).

    (** We could derive [SMethod_mono] from the following
        [SMethod_wpspec_monoN]. We retain this proof because it's easier
        to understand and it goes through without [BiEntailsN]. *)
    #[local] Lemma SMethodOptCast_mono cast wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp2 this) (wpp1 this)) ->
      fs_entails
        (SMethodOptCast (cc:=cc) class cast qual ret targs wpp1)
        (SMethodOptCast (cc:=cc) class cast qual ret targs wpp2).
    Proof.
      intros Hwpp.
      apply SFunction_mono => vs K.
      rewrite /= /exact_spec.
      f_equiv => this.
      move: Hwpp.
      match goal with
      | |- context [ spec_internal _ (?A :: nil) _ _ _ _ ] =>
          change (A :: nil) with ([] ++ [A])
      end.
      rewrite !arg_ok.
      intros.
      apply bi.exist_mono; intro.
      apply bi.sep_mono; eauto.
      apply Hwpp.
    Qed.

    Lemma SMethodCast_mono cast wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp2 this) (wpp1 this)) ->
      fs_entails
        (SMethodOptCast (cc:=cc) class cast qual ret targs wpp1)
        (SMethodOptCast (cc:=cc) class cast qual ret targs wpp2).
    Proof. exact: SMethodOptCast_mono. Qed.

    Lemma SMethod_mono wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp2 this) (wpp1 this)) ->
      fs_entails
        (SMethod (cc:=cc) class qual ret targs wpp1)
        (SMethod (cc:=cc) class qual ret targs wpp2).
    Proof. exact: SMethodOptCast_mono. Qed.

    #[local] Lemma SMethodOptCast_wpspec_monoN
        c wpp1 wpp2 vs K n :
      (∀ this, wpspec_entailsN n (wpp1 this) (wpp2 this)) ->
      SMethodOptCast_wpp c wpp1 vs K ⊢{n}
      SMethodOptCast_wpp c wpp2 vs K.
    Proof.
      move=>Hwpp /=. rewrite /exact_spec. f_equiv=>this.
      match goal with
      | |- context [ ?A :: nil ] =>
          change (A :: nil) with ([] ++ [A])
      end.
      rewrite !arg_ok.
      f_equiv. intro.
      f_equiv.
      apply Hwpp.
    Qed.

    #[local] Lemma SMethodOptCast_ne cast wpp1 wpp2 n :
      (∀ this, wpspec_dist n (wpp1 this) (wpp2 this)) ->
      SMethodOptCast (cc:=cc) class cast qual ret targs wpp1 ≡{n}≡
      SMethodOptCast (cc:=cc) class cast qual ret targs wpp2.
    Proof.
      setoid_rewrite wpspec_dist_entailsN=>Hwpp.
      rewrite/SMethodOptCast. f_equiv=>vs K /=. apply dist_entailsN.
      split; apply SMethodOptCast_wpspec_monoN=>this; by destruct (Hwpp this).
    Qed.

    Lemma SMethodCast_ne cast wpp1 wpp2 n :
      (∀ this, wpspec_dist n (wpp1 this) (wpp2 this)) ->
      SMethodCast (cc:=cc) class cast qual ret targs wpp1 ≡{n}≡
      SMethodCast (cc:=cc) class cast qual ret targs wpp2.
    Proof. exact: SMethodOptCast_ne. Qed.

    Lemma SMethod_ne wpp1 wpp2 n :
      (∀ this, wpspec_dist n (wpp1 this) (wpp2 this)) ->
      SMethod (cc:=cc) class qual ret targs wpp1 ≡{n}≡
      SMethod (cc:=cc) class qual ret targs wpp2.
    Proof. exact: SMethodOptCast_ne. Qed.

    #[local] Lemma SMethodOptCast_proper cast wpp1 wpp2 :
      (∀ this, wpspec_equiv (wpp1 this) (wpp2 this)) ->
      SMethodOptCast (cc:=cc) class cast qual ret targs wpp1 ≡
      SMethodOptCast (cc:=cc) class cast qual ret targs wpp2.
    Proof.
      setoid_rewrite wpspec_equiv_spec=>Hwpp. apply function_spec_equiv_split.
      split; apply SMethodCast_mono=>this; by destruct (Hwpp this).
    Qed.
    Lemma SMethodCast_proper cast wpp1 wpp2 :
      (∀ this, wpspec_equiv (wpp1 this) (wpp2 this)) ->
      SMethodCast (cc:=cc) class cast qual ret targs wpp1 ≡
      SMethodCast (cc:=cc) class cast qual ret targs wpp2.
    Proof. exact: SMethodOptCast_proper. Qed.
    Lemma SMethod_proper wpp1 wpp2 :
      (∀ this, wpspec_equiv (wpp1 this) (wpp2 this)) ->
      SMethod (cc:=cc) class qual ret targs wpp1 ≡
      SMethod (cc:=cc) class qual ret targs wpp2.
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

    #[global] Instance SMethodCast_mono' cast :
      Proper (pointwise_relation _ (flip wpspec_entails) ==> fs_entails)
        (SMethodCast (cc:=cc) class cast qual ret targs).
    Proof. repeat intro. by apply SMethodCast_mono. Qed.
    #[global] Instance SMethod_mono' :
      Proper (pointwise_relation _ (flip wpspec_entails) ==> fs_entails)
        (SMethod (cc:=cc) class qual ret targs).
    Proof. repeat intro. by apply SMethod_mono. Qed.

    #[global] Instance SMethodCast_flip_mono' cast :
      Proper (pointwise_relation _ wpspec_entails ==> flip fs_entails)
        (SMethodCast (cc:=cc) class cast qual ret targs).
    Proof. repeat intro. by apply SMethodCast_mono. Qed.
    #[global] Instance SMethod_flip_mono' :
      Proper (pointwise_relation _ wpspec_entails ==> flip fs_entails)
        (SMethod (cc:=cc) class qual ret targs).
    Proof. repeat intro. by apply SMethod_mono. Qed.
  End SMethod.

End with_cpp.
