(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.NArith.BinNatDef.
From Coq.Strings Require Import
     Ascii String.
Require Import Coq.ZArith.BinIntDef.

Require Import Cpp.Util.
From Cpp.Syntax Require Import Names Types Expr.

Set Primitive Projections.

Variant SwitchBranch : Set :=
| Exact (_ : Z)
| Range (_ _ : Z)
.

Record VarDecl : Set :=
{ vd_name : ident
; vd_type : type
; vd_init : option Expr
; vd_dtor : option obj_name
}.


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

| Sattr (_ : list string) (_ : Stmt)

| Sasm (_ : string) (volatile : bool)
       (inputs : list (string * Expr))
       (outputs : list (string * Expr))
       (clobbers : list string)

| Slabeled (_ : string) (_ : Stmt)
| Sgoto (_ : string)
.

Definition Sskip := Sseq nil.



Variant OrDefault {t : Set} : Set :=
| Defaulted
| UserDefined (_ : t).
Arguments OrDefault : clear implicits.

Variant FieldOrBase : Set :=
| Base (_ : globname)
| Field (_ : ident)
| Indirect (anon_path : list (ident * globname)) (_ : ident)
| This.

Record Initializer :=
  { init_path : FieldOrBase
  ; init_type : type
  ; init_init : Expr }.

Definition Stmt_eq_dec : forall a b : Stmt, {a = b} + {a <> b}.
Proof.
  generalize type_eq_dec.
  generalize (fun a b => @Decidable_dec _ _ _ (Decidable_eq_VarRef a b)).
  generalize BinInt.Z.eq_dec.
  generalize ascii_dec.
  generalize string_dec.
  generalize Bool.bool_dec.
  generalize (fun a b => @Decidable_dec _ _ _ (Decidable_eq_UnOp a b)).
  generalize (fun a b => @Decidable_dec _ _ _ (Decidable_eq_BinOp a b)).
  generalize (fun a b => @Decidable_dec _ _ _ (Decidable_eq_ValCat a b)).
  generalize Expr_eq_dec.
  do 10 intro.
  refine (fix Stmt_dec a b : {a = b} + {a <> b} :=
            _).
  decide equality.
  all: try eapply List.list_eq_dec.
  all: try eassumption.
  all: decide equality.
  all: decide equality.
  all: decide equality.
Defined.

Global Instance Decidable_eq_Stmt (a b : Stmt) : Decidable (a = b) :=
  dec_Decidable (Stmt_eq_dec a b).

Global Instance Decidable_FieldOrBase (a b : FieldOrBase) : Decidable (a = b).
Proof.
  refine {| Decidable_witness :=
              match a , b with
              | Base a , Base b => decide (a = b)
              | Field a , Field b => decide (a = b)
              | Indirect a a' , Indirect b b' => decide (a = b) && decide (a' = b')
              | This , This => true
              | _ , _ => false
              end |}.
  destruct a; destruct b; repeat rewrite Bool.andb_true_iff; repeat rewrite decide_ok; try solve [ split; congruence ].
  firstorder; congruence.
Defined.
