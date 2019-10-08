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

From iris.proofmode Require Import tactics.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Logic Semantics.

(* expression continuations
 * - in full C++, this includes exceptions, but our current semantics
 *   doesn't treat those.
 *)
Definition epred Σ := mpred Σ.

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

Definition FreeTemps Σ := mpred Σ.
(** Expressions *)
Section with_Σ.
Context {Σ : gFunctors}.

Notation mpred := (mpred Σ) (only parsing).
Notation FreeTemps := (FreeTemps Σ) (only parsing).
Notation epred := (epred Σ) (only parsing).

(* [SP] denotes the sequence point for an expression *)
Definition SP (Q : val -> mpred) (v : val) (free : FreeTemps) : mpred :=
  free ** Q v.

(* evaluate an expression as an lvalue *)
Parameter wp_lval
  : forall {resolve : genv},
    thread_info -> region ->
    Expr ->
    (val -> FreeTemps -> epred) -> (* result -> free -> post *)
    mpred. (* pre-condition *)

Axiom Proper_wp_lval : forall resolve ti r e,
    Proper ((pointwise_relation _ (pointwise_relation _ lentails)) ==> lentails)
           (@wp_lval resolve ti r e).
Global Existing Instance Proper_wp_lval.

(* evaluate an expression as an prvalue *)
Parameter wp_prval
  : forall {resolve : genv},
    thread_info -> region ->
    Expr ->
    (val -> FreeTemps -> epred) -> (* result -> free -> post *)
    mpred. (* pre-condition *)

Axiom Proper_wp_prval : forall resolve ti r e,
    Proper ((pointwise_relation _ (pointwise_relation _ lentails)) ==> lentails)
           (@wp_prval resolve ti r e).
Global Existing Instance Proper_wp_prval.

(* evaluate an initializing expression
 * - the [val] is the location of the value that is being initialized
 * - the expression denotes a prvalue with a "result object" (see
 *    https://en.cppreference.com/w/cpp/language/value_category)
 *)
Parameter wp_init
  : forall {resolve : genv},
    thread_info -> region ->
    type -> val -> Expr ->
    (FreeTemps -> epred) -> (* free -> post *)
    mpred. (* pre-condition *)
Axiom Proper_wp_init : forall resolve ti r ty addr e,
    Proper (pointwise_relation _ lentails ==> lentails)
           (@wp_init resolve ti r ty addr e).
Global Existing Instance Proper_wp_init.


(* evaluate an expression as an xvalue *)
Parameter wp_xval
  : forall {resolve : genv},
    thread_info -> region ->
    Expr ->
    (val -> FreeTemps -> epred) -> (* result -> free -> post *)
    mpred. (* pre-condition *)

Axiom Proper_wp_xval : forall resolve ti r e,
    Proper ((pointwise_relation _ (pointwise_relation _ lentails)) ==> lentails)
           (@wp_xval resolve ti r e).
Global Existing Instance Proper_wp_xval.

Definition wp_glval {resolve : genv} (ti : thread_info) (r : region) e Q :=
  wp_lval (resolve:=resolve) ti r e Q \\//
  wp_xval (resolve:=resolve) ti r e Q.
Theorem Proper_wp_glval : forall resolve ti r e,
    Proper ((pointwise_relation _ (pointwise_relation _ lentails)) ==> lentails)
           (@wp_glval resolve ti r e).
Proof.
  unfold wp_glval; simpl. do 2 red. intros.
  rewrite -> H. eauto.
Qed.
Global Existing Instance Proper_wp_glval.


Definition wp_rval {resolve : genv} (ti : thread_info) (r : region) e Q :=
  wp_prval (resolve:=resolve) ti r e Q \\//
  wp_xval (resolve:=resolve) ti r e Q.
Theorem Proper_wp_rval : forall resolve ti r e,
    Proper ((pointwise_relation _ (pointwise_relation _ lentails)) ==> lentails)
           (@wp_rval resolve ti r e).
Proof.
  unfold wp_rval; simpl. do 2 red. intros.
  rewrite -> H. eauto.
Qed.
Global Existing Instance Proper_wp_rval.

Section wpe.
  Context {resolve : genv}.
  Variable ti : thread_info.
  Variable ρ : region.

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
End with_Σ.

(** Statements *)
(* continuations
 * C++ statements can terminate in 4 ways.
 *
 * note(gmm): technically, they can also raise exceptions; however,
 * our current semantics doesn't capture this. if we want to support
 * exceptions, we should be able to add another case,
 * `k_throw : val -> mpred`.
 *)
Record Kpreds Σ :=
  { k_normal   : mpred Σ
  ; k_return   : option val -> FreeTemps Σ -> mpred Σ
  ; k_break    : mpred Σ
  ; k_continue : mpred Σ
  }.
Arguments k_normal {_}.
Arguments k_return {_} _ _.
Arguments k_break {_}.
Arguments k_continue {_}.

Section with_Σ.
Context `{Σ : gFunctors}.

Notation mpred := (mpred Σ) (only parsing).
Notation FreeTemps := (FreeTemps Σ) (only parsing).
Notation Kpreds := (Kpreds Σ) (only parsing).

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

Definition Kseq (Q : mpred) (k : Kpreds) : Kpreds :=
  {| k_normal   := Q
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

Instance Kpreds_equiv : Equiv Kpreds :=
  fun (k1 k2 : Kpreds) =>
    k1.(k_normal) ≡ k2.(k_normal) ∧
    (∀ v free, k1.(k_return) v free ≡ k2.(k_return) v free) ∧
    k1.(k_break) ≡ k2.(k_break) ∧
    k1.(k_continue) ≡ k2.(k_continue).

(* evaluate a statement *)
Parameter wp
  : forall {resolve : genv}, thread_info -> region -> Stmt -> Kpreds -> mpred.

Axiom Proper_wp : forall resolve ti r e,
    Proper (equiv ==> lentails)
           (@wp resolve ti r e).
Global Existing Instance Proper_wp.

(* note: the [list val] here represents the *locations* of the parameters, not
 * their values.
 * todo(gmm): this isn't currently true, but it should be true
 *)
Parameter func_ok_raw
  : forall {resolve: genv}, thread_info -> Func -> list val -> (val -> mpred) -> mpred.

(* todo(gmm): this is because func_ok is implemented using wp. *)
Axiom func_ok_raw_conseq:
  forall {resolve} ti f vs (Q Q' : val -> mpred),
    (forall r : val, Q r |-- Q' r) ->
    func_ok_raw (resolve:=resolve) ti f vs Q |-- func_ok_raw (resolve:=resolve) ti f vs Q'.

Definition fspec {resolve} (n : val) (ls : list val) (ti : thread_info) (Q : val -> mpred) : mpred :=
  Exists f, [| n = Vptr f |] **
  Exists func, code_at func f ** func_ok_raw (resolve:=resolve) ti func ls Q.

Theorem fspec_ok_conseq:
  forall {resolve} (p : val) (vs : list val) ti (K m : val -> mpred),
    (forall r : val, m r |-- K r) ->
    fspec (resolve:=resolve) p vs ti m |-- fspec (resolve:=resolve) p vs ti K.
Proof.
  intros. unfold fspec.
  iIntros "H". iDestruct "H" as (f) "[-> H]".
  iExists f. iSplitR; [ iPureIntro; eauto | ].
  iDestruct "H" as (func) "[Hca Hor]".
  iExists func. iFrame.
  rewrite func_ok_raw_conseq; eauto.
Qed.

End with_Σ.
