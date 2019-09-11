(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * Definitions for the semantics
 *
 *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     ChargeUtil Logic Semantics.
From Cpp.Syntax Require Import
     Stmt.

(* expression continuations
 * - in full C++, this includes exceptions, but our current semantics
 *   doesn't treat those.
 *)
Definition epred := mpred.

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


(** Expressions *)
Definition FreeTemps := mpred.

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
  eapply lor_lentails_m; [ eapply Proper_wp_lval | eapply Proper_wp_xval ]; eauto.
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
  eapply lor_lentails_m; [ eapply Proper_wp_prval | eapply Proper_wp_xval ]; eauto.
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



Global Instance ILogicOps_Kpreds : ILogicOps Kpreds :=
{ lentails P Q :=
    P.(k_normal) |-- Q.(k_normal) /\
    P.(k_break) |-- Q.(k_break) /\
    P.(k_continue) |-- Q.(k_continue) /\
    forall x f, P.(k_return) x f |-- Q.(k_return) x f
; ltrue :=
    {| k_normal := ltrue
     ; k_break := ltrue
     ; k_continue := ltrue
     ; k_return _ := ltrue |}
; lfalse :=
    {| k_normal := lfalse
     ; k_break := lfalse
     ; k_continue := lfalse
     ; k_return _ := lfalse |}

; land  P Q :=
    {| k_normal   := land P.(k_normal) Q.(k_normal)
     ; k_break    := land P.(k_break) Q.(k_break)
     ; k_continue := land P.(k_continue) Q.(k_continue)
     ; k_return v := land (P.(k_return) v) (Q.(k_return) v) |}

; lor   P Q :=
    {| k_normal   := lor P.(k_normal) Q.(k_normal)
     ; k_break    := lor P.(k_break) Q.(k_break)
     ; k_continue := lor P.(k_continue) Q.(k_continue)
     ; k_return v := lor (P.(k_return) v) (Q.(k_return) v) |}

; limpl P Q :=
    {| k_normal   := limpl P.(k_normal) Q.(k_normal)
     ; k_break    := limpl P.(k_break) Q.(k_break)
     ; k_continue := limpl P.(k_continue) Q.(k_continue)
     ; k_return v := limpl (P.(k_return) v) (Q.(k_return) v) |}

; lforall T P :=
    {| k_normal   := lforall (fun x : T => (P x).(k_normal))
     ; k_break    := lforall (fun x : T => (P x).(k_break))
     ; k_continue := lforall (fun x : T => (P x).(k_continue))
     ; k_return v := lforall (fun x : T => (P x).(k_return) v) |}

; lexists T P :=
    {| k_normal   := lexists (fun x : T => (P x).(k_normal))
     ; k_break    := lexists (fun x : T => (P x).(k_break))
     ; k_continue := lexists (fun x : T => (P x).(k_continue))
     ; k_return v := lexists (fun x : T => (P x).(k_return) v) |}
}.
Global Instance ILogic_Kpreds : ILogic Kpreds.
Proof.
  Transparent ILInsts.ILFun_Ops.
  constructor; try red; simpl.
  { constructor.
    - red. firstorder.
    - red. firstorder; etransitivity; eauto. }
  all: try solve [ firstorder; eauto using ltrueR, lfalseL, landL1, landL2, landR, lorL , lorR1, lorR2, limplAdj, landAdj, lforallL, lforallR, lexistsL, lexistsR ].
  { firstorder; eapply lforallR; intros; eapply H. }
  { firstorder; eapply lexistsL; intros; eapply H. }
  Opaque ILInsts.ILFun_Ops.
Qed.
Global Instance BILogicOps_Kpreds : BILogicOps Kpreds :=
{ empSP      :=
    {| k_normal   := empSP
     ; k_break    := empSP
     ; k_continue := empSP
     ; k_return _ _ := empSP |}

; sepSP  P Q :=
    {| k_normal   := sepSP P.(k_normal) Q.(k_normal)
     ; k_break    := sepSP P.(k_break) Q.(k_break)
     ; k_continue := sepSP P.(k_continue) Q.(k_continue)
     ; k_return v f := sepSP (P.(k_return) v f) (Q.(k_return) v f) |}

; wandSP P Q :=
    {| k_normal   := wandSP P.(k_normal) Q.(k_normal)
     ; k_break    := wandSP P.(k_break) Q.(k_break)
     ; k_continue := wandSP P.(k_continue) Q.(k_continue)
     ; k_return v f := wandSP (P.(k_return) v f) (Q.(k_return) v f) |}

}.
Global Instance BILogic_Kpreds : BILogic Kpreds.
Proof.
  constructor; try red; simpl; eauto with typeclass_instances.
  all: try solve [ firstorder; eauto using sepSPC1, sepSPA1, bilsep, empSPR, wandSepSPAdj ].
  { firstorder; eapply wandSepSPAdj; eauto. }
  { firstorder; eapply empSPR; eauto. }
Qed.

(* evaluate a statement *)
Parameter wp
  : forall {resolve : genv}, thread_info -> region -> Stmt -> Kpreds -> mpred.

Axiom Proper_wp : forall resolve ti r e,
    Proper (lentails ==> lentails)
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
  eapply lexists_lentails_m. red; intros.
  eapply scME; [ reflexivity | ].
  eapply lexists_lentails_m. red; intros.
  eapply scME; [ reflexivity | ].
  eapply func_ok_raw_conseq. assumption.
Qed.
