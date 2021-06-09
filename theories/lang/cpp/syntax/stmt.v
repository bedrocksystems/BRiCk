(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
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

| Sswitch (_ : option VarDecl) (_ : Expr) (_ : Stmt)
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
  rewrite /RelDecision /Decision.
  fix IHs 1.
  rewrite -{1}/(EqDecision Stmt) in IHs.
  decide equality; try solve_trivial_decision.
Defined.

Definition Sskip := Sseq nil.



Variant OrDefault {t : Set} : Set :=
| Defaulted
| UserDefined (_ : t).
Arguments OrDefault : clear implicits.

Instance OrDefault_eq_dec: forall {T: Set}, EqDecision T -> EqDecision (OrDefault T).
Proof. solve_decision. Defined.
