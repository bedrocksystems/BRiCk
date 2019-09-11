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
Require Import Cpp.Syntax.Ast.
Require Import Cpp.Syntax.Types.

Set Primitive Projections.

Variant UnOp : Set :=
| Uminus
| Unot
| Ubnot
| Uother (_ : string).
Global Instance Decidable_eq_UnOp (a b : UnOp) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).

Variant BinOp : Set :=
| Badd
| Band (* & *)
| Bcmp (* <=> *)
| Bdiv (* / *)
| Beq
| Bge
| Bgt
| Ble
| Blt
| Bmul
| Bneq
| Bor  (* | *)
| Bmod
| Bshl
| Bshr
| Bsub
| Bxor (* ^ *)
.
Global Instance Decidable_eq_BinOp (a b : BinOp) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).

Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).
Global Instance Decidable_eq_VarRef (a b : VarRef) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).


Variant ValCat : Set := Lvalue | Rvalue | Xvalue.
Global Instance Decidable_eq_ValCat (a b : ValCat) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).


Variant AtomicOp : Set :=
| AO__atomic_load
| AO__atomic_load_n
| AO__atomic_store
| AO__atomic_store_n
| AO__atomic_compare_exchange
| AO__atomic_compare_exchange_n
| AO__atomic_exchange
| AO__atomic_exchange_n
| AO__atomic_fetch_add
| AO__atomic_fetch_sub
| AO__atomic_fetch_and
| AO__atomic_fetch_or
| AO__atomic_fetch_xor
| AO__atomic_fetch_nand
| AO__atomic_add_fetch
| AO__atomic_sub_fetch
| AO__atomic_and_fetch
| AO__atomic_or_fetch
| AO__atomic_xor_fetch
| AO__atomic_nand_fetch
.
Global Instance Decidable_eq_AtomicOp (a b : AtomicOp) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).

Inductive Expr : Set :=
| Econst_ref (_ : VarRef) (_ : type)
  (* ^ these are different because they do not have addresses *)
| Evar     (_ : VarRef) (_ : type)
  (* ^ local variable reference *)

| Echar    (_ : Ascii.ascii) (_ : type)
| Estring  (_ : String.string) (_ : type)
| Eint     (_ : Z) (_ : type)
| Ebool    (_ : bool)
  (* ^ literals *)

| Eunop    (_ : UnOp) (_ : Expr) (_ : type)
| Ebinop   (_ : BinOp) (_ _ : Expr) (_ : type)
 (* ^ note(gmm): overloaded operators are already resolved. so an overloaded
  * operator shows up as a function call, not a `Eunop` or `Ebinop`.
  * this includes the assignment operator for classes.
  *)
| Ederef (_ : Expr) (_ : type)
| Eaddrof (_ : Expr) (_ : type)
| Eassign (_ _ : Expr) (_ : type)
| Eassign_op (_ : BinOp) (_ _ : Expr) (_ : type)
  (* ^ these are specialized because they are common *)

| Epreinc (_ : Expr) (_ : type)
| Epostinc (_ : Expr) (_ : type)
| Epredec (_ : Expr) (_ : type)
| Epostdec (_ : Expr) (_ : type)
  (* ^ special unary operators *)

| Eseqand (_ _ : Expr) (_ : type)
| Eseqor  (_ _ : Expr) (_ : type)
| Ecomma (vc : ValCat) (_ _ : Expr) (_ : type)
  (* ^ these are specialized because they have special control flow semantics *)

| Ecall    (_ : Expr) (_ : list (ValCat * Expr)) (_ : type)
| Ecast    (_ : Cast) (_ : ValCat * Expr) (_ : type)

| Emember  (obj : Expr) (_ : field) (_ : type)
| Emember_call (is_virtual : bool) (method : globname) (obj : Expr) (_ : list (ValCat * Expr)) (_ : type)

| Esubscript (_ : Expr) (_ : Expr) (_ : type)
| Esize_of (_ : type + Expr) (_ : type)
| Ealign_of (_ : type + Expr) (_ : type)
| Econstructor (_ : globname) (_ : list (ValCat * Expr)) (_ : type)
| Eimplicit (_ : Expr) (_ : type)
| Eimplicit_init (_ : type)
| Eif       (_ _ _ : Expr) (_ : type)

| Ethis (_ : type)
| Enull
| Einitlist (_ : list Expr) (_ : option Expr) (_ : type)

| Enew (_ : option globname) (array_size : option Expr) (init : option Expr) (_ : type)
| Edelete (is_array : bool) (_ : option globname) (_ : Expr) (_ : type)

| Eandclean (_ : Expr) (_ : type)
| Ematerialize_temp (_ : Expr) (_ : type)
| Ebind_temp (_ : Expr) (_ : obj_name) (_ : type)

| Eatomic (_ : AtomicOp) (_ : list (ValCat * Expr)) (_ : type)
| Eva_arg (_ : Expr) (_ : type)
| Eunsupported (_ : string) (_ : type)
.

Definition Edefault_init_expr (e : Expr) : Expr := e.


Definition Expr_eq_dec : forall a b : Expr, {a = b} + {a <> b}.
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
  do 9 intro.
  refine (fix Expr_dec a b : {a = b} + {a <> b} :=
             _).
  decide equality.
  all: try eapply List.list_eq_dec.
  all: decide equality.
  all: decide equality.
  all: decide equality.
Defined.

Global Instance Decidable_eq_Expr (a b : Expr) : Decidable (a = b) :=
  dec_Decidable (Expr_eq_dec a b).
