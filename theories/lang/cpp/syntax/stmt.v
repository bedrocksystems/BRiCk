(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import stdpp.decidable.
Require Import stdpp.numbers.
From bedrock.lang.cpp.syntax Require Import names types expr.
Require Import bedrock.lang.prelude.bytestring.

Set Primitive Projections.

Variant SwitchBranch : Set :=
| Exact (_ : Z)
| Range (_ _ : Z).
Instance: EqDecision SwitchBranch.
Proof. solve_decision. Defined.

Record VarDecl : Set :=
{ vd_name : ident
; vd_type : type
; vd_init : option Expr
; vd_dtor : option obj_name
}.
Instance: EqDecision VarDecl.
Proof. solve_decision. Defined.


Inductive Stmt : Set :=
| Sseq    (_ : list Stmt)
| Sdecl   (_ : list VarDecl)

| Sif     (_ : option VarDecl) (_ : Expr) (_ _ : Stmt)
| Swhile  (_ : option VarDecl) (_ : Expr) (_ : Stmt)
| Sfor    (_ : option Stmt) (_ : option Expr) (_ : option (ValCat * Expr)) (_ : Stmt)
| Sdo     (_ : Stmt) (_ : Expr)

| Sswitch (_ : Expr) (_ : Stmt)
| Scase   (_ : SwitchBranch)
| Sdefault

| Sbreak
| Scontinue

| Sreturn (_ : option (ValCat * Expr))

| Sexpr   (_ : ValCat) (_ : Expr)

| Sattr (_ : list ident) (_ : Stmt)

| Sasm (_ : bs) (volatile : bool)
       (inputs : list (ident * Expr))
       (outputs : list (ident * Expr))
       (clobbers : list ident)

| Slabeled (_ : ident) (_ : Stmt)
| Sgoto (_ : ident)
| Sunsupported (_ : bs).
Instance Stmt_eq_dec : EqDecision Stmt.
Proof.
  do 2 red.
  fix IHS 1.
  decide equality; try solve_trivial_decision.
  all: try apply list_eq_dec; try apply IHS.
  apply decide; eapply option_eq_dec.
  Unshelve. exact IHS.
Defined.

Definition Sskip := Sseq nil.



Variant OrDefault {t : Set} : Set :=
| Defaulted
| UserDefined (_ : t).
Arguments OrDefault : clear implicits.

Instance OrDefault_eq_dec: forall {T: Set}, EqDecision T -> EqDecision (OrDefault T).
Proof. solve_decision. Defined.


Variant FieldOrBase : Set :=
| Base (_ : globname)
| Field (_ : ident)
| Indirect (anon_path : list (ident * globname)) (_ : ident)
| This.
Instance: EqDecision FieldOrBase.
Proof. solve_decision. Defined.


Record Initializer :=
  { init_path : FieldOrBase
  ; init_type : type
  ; init_init : Expr }.
Instance: EqDecision Initializer.
Proof. solve_decision. Defined.
