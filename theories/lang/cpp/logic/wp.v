(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * Definitions for the semantics
 *
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import iris.bi.monpred.
From iris.proofmode Require Import tactics.

From bedrock.lang.cpp Require Import
     ast semantics logic.pred.

Set Primitive Projections.

(* this applies `wp` across a list
 *
 * note(gmm): we consistently use this for evaluating arguments, so it should
 * reflect parallel evaluation
 *)
Section wps.
  Context {T U V : Type}.
  Variable wp : T -> (U -> V) -> V.

  Fixpoint wps (es : list T) (Q : list U -> V) : V :=
    match es with
    | nil => Q nil
    | e :: es => wp e (fun v => wps es (fun vs => Q (cons v vs)))
    end.
End wps.


Section with_cpp.
  Context `{Σ : cpp_logic thread_info}.

  (* expression continuations
   * - in full C++, this includes exceptions, but our current semantics
   *   doesn't treat those.
   *)
  Definition epred := mpred.

  Definition FreeTemps := mpred.

  (* [SP] denotes the sequence point for an expression *)
  Definition SP (Q : val -> mpred) (v : val) (free : FreeTemps) : mpred :=
    free ** Q v.

  (* evaluate an expression as an lvalue *)
  Parameter wp_lval
    : forall {resolve:genv}, thread_info -> region ->
        Expr ->
        (val -> FreeTemps -> epred) -> (* result -> free -> post *)
        mpred. (* pre-condition *)

  Axiom Proper_wp_lval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_lval).
  Global Existing Instance Proper_wp_lval.

  (* evaluate an expression as an prvalue *)
  Parameter wp_prval
    : forall {resolve:genv}, thread_info -> region ->
        Expr ->
        (val -> FreeTemps -> epred) -> (* result -> free -> post *)
        mpred. (* pre-condition *)

  Axiom Proper_wp_prval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_prval).
  Global Existing Instance Proper_wp_prval.

  (* evaluate an initializing expression
   * - the [val] is the location of the value that is being initialized
   * - the expression denotes a prvalue with a "result object" (see
   *    https://en.cppreference.com/w/cpp/language/value_category)
   *)
  Parameter wp_init
    : forall {resolve:genv}, thread_info -> region ->
                        type -> val -> Expr ->
                        (FreeTemps -> epred) -> (* free -> post *)
                        mpred. (* pre-condition *)
  Axiom Proper_wp_init :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ lentails ==> lentails)
           (@wp_init).
  Global Existing Instance Proper_wp_init.


  (* evaluate an expression as an xvalue *)
  Parameter wp_xval
    : forall {resolve:genv}, thread_info -> region ->
                        Expr ->
                        (val -> FreeTemps -> epred) -> (* result -> free -> post *)
                        mpred. (* pre-condition *)

  Axiom Proper_wp_xval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_xval).
  Global Existing Instance Proper_wp_xval.

  Definition wp_glval {resolve} ti (r : region) e Q :=
    @wp_lval resolve ti r e Q \\// @wp_xval resolve ti r e Q.
  Theorem Proper_wp_glval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_glval).
  Proof.
    unfold wp_glval; simpl. do 6 red. intros.
    eapply bi.or_elim; [ rewrite <- bi.or_intro_l | rewrite <- bi.or_intro_r ].
    eapply Proper_wp_lval; eauto.
    eapply Proper_wp_xval; eauto.
  Qed.
  Global Existing Instance Proper_wp_glval.


  Definition wp_rval {resolve} ti (r : region) e Q :=
    @wp_prval resolve ti r e Q \\// @wp_xval resolve ti r e Q.
  Theorem Proper_wp_rval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_rval).
  Proof.
    unfold wp_rval; simpl. do 6 red. intros.
    eapply bi.or_elim; [ rewrite <- bi.or_intro_l | rewrite <- bi.or_intro_r ].
    eapply Proper_wp_prval; eauto.
    eapply Proper_wp_xval; eauto.
  Qed.
  Global Existing Instance Proper_wp_rval.

  Section wpe.
    Context {resolve:genv}.
    Variable (ti : thread_info) (ρ : region).

    Definition wpe (vc : ValCat)
      : Expr -> (val -> FreeTemps -> mpred) -> mpred :=
      match vc with
      | Lvalue => @wp_lval resolve ti ρ
      | Rvalue => @wp_prval resolve ti ρ
      | Xvalue => @wp_xval resolve ti ρ
      end.

    Definition wpAny (vce : ValCat * Expr)
      : (val -> FreeTemps -> mpred) -> mpred :=
      let '(vc,e) := vce in
      wpe vc e.

    Definition wpAnys := fun ve Q free => wpAny ve (fun v f => Q v (f ** free)).
  End wpe.

  (** initializers *)
  Parameter wpi
    : forall {resolve:genv} (ti : thread_info) (ρ : region)
        (cls : globname) (this : val) (init : Initializer)
        (Q : mpred -> mpred), mpred.

  Axiom Proper_wpi :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> eq ==> (lentails ==> lentails) ==> lentails)
           (@wpi).
  Global Existing Instance Proper_wp_prval.

  (** destructors *)
  Parameter wpd
    : forall {resolve:genv} (ti : thread_info) (ρ : region)
        (cls : globname) (this : val)
        (init : FieldOrBase * obj_name)
        (Q : epred), mpred.

  (** Statements *)
  (* continuations
   * C++ statements can terminate in 4 ways.
   *
   * note(gmm): technically, they can also raise exceptions; however,
   * our current semantics doesn't capture this. if we want to support
   * exceptions, we should be able to add another case,
   * `k_throw : val -> mpred`.
   *)
  Record Kpreds :=
    { k_normal   : mpred
    ; k_return   : option val -> FreeTemps -> mpred
    ; k_break    : mpred
    ; k_continue : mpred
    }.

  Definition void_return (P : mpred) : Kpreds :=
    {| k_normal := P
     ; k_return := fun r free => match r with
                              | None => free ** P
                              | Some _ => lfalse
                              end
     ; k_break := lfalse
     ; k_continue := lfalse
    |}.

  Definition val_return (P : val -> mpred) : Kpreds :=
    {| k_normal := lfalse
     ; k_return := fun r free => match r with
                              | None => lfalse
                              | Some v => free ** P v
                              end
     ; k_break := lfalse
     ; k_continue := lfalse |}.

  Definition Kseq (Q : Kpreds -> mpred) (k : Kpreds) : Kpreds :=
    {| k_normal   := Q k
     ; k_return   := k.(k_return)
     ; k_break    := k.(k_break)
     ; k_continue := k.(k_continue) |}.

  (* loop with invariant `I` *)
  Definition Kloop (I : mpred) (Q : Kpreds) : Kpreds :=
    {| k_break    := Q.(k_normal)
     ; k_continue := I
     ; k_return   := Q.(k_return)
     ; k_normal   := Q.(k_normal) |}.

  Definition Kat_exit (Q : mpred -> mpred) (k : Kpreds) : Kpreds :=
    {| k_normal   := Q k.(k_normal)
     ; k_return v free := Q (k.(k_return) v free)
     ; k_break    := Q k.(k_break)
     ; k_continue := Q k.(k_continue) |}.

  Definition Kfree (a : mpred) : Kpreds -> Kpreds :=
    Kat_exit (fun P => a ** P).

  Global Instance Kpreds_equiv : Equiv Kpreds :=
    fun (k1 k2 : Kpreds) =>
      k1.(k_normal) ≡ k2.(k_normal) ∧
      (∀ v free, k1.(k_return) v free ≡ k2.(k_return) v free) ∧
      k1.(k_break) ≡ k2.(k_break) ∧
      k1.(k_continue) ≡ k2.(k_continue).

  Lemma Kfree_Kfree : forall k P Q, Kfree P (Kfree Q k) ≡ Kfree (P ** Q) k.
  Proof.
    split; [ | split; [ | split ] ]; simpl; intros;
      eapply bi.equiv_spec; split;
        try solve [ rewrite bi.sep_assoc; eauto ].
  Qed.

  Lemma Kfree_emp : forall k, Kfree empSP k ≡ k.
  Proof.
    split; [ | split; [ | split ] ]; simpl; intros;
      eapply bi.equiv_spec; split;
        try solve [ rewrite bi.emp_sep; eauto ].
  Qed.

  (* evaluate a statement *)
  Parameter wp
    : forall {resolve:genv}, thread_info -> region -> Stmt -> Kpreds -> mpred.

  Axiom Proper_wp :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> equiv ==> lentails)
           (@wp).
  Global Existing Instance Proper_wp.

  (* this is the *semantic characterization* of a function
   * it really says something about the assembly code
   *
   * [addr] represents the address of the entry point of the code.
   *)
  Parameter fspec
    : forall (ti : thread_info) (addr : val) (ls : list val) (Q : val -> epred), mpred.
  (* ^ todo(gmm): is this correct? *)

  Axiom Proper_fspec : forall a ls ti,
      Proper (pointwise_relation _ lentails ==> lentails) (@fspec ti a ls).
End with_cpp.
