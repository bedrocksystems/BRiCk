(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import stdpp.decidable.
Require Import stdpp.strings.
Require Import bedrock.Util.
From bedrock.lang.cpp.syntax Require Import names types.

Set Primitive Projections.

Variant UnOp : Set :=
| Uminus
| Unot
| Ubnot
| Uother (_ : bs).
Instance: EqDecision UnOp.
Proof. solve_decision. Defined.

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
| Bdotp (* .* *)
| Bdotip (* ->* *)
.
Instance: EqDecision BinOp.
Proof. solve_decision. Defined.

Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).
Instance: EqDecision VarRef.
Proof. solve_decision. Defined.

Variant ValCat : Set := Lvalue | Rvalue | Xvalue.
Instance: EqDecision ValCat.
Proof. solve_decision. Defined.

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
Instance: EqDecision AtomicOp.
Proof. solve_decision. Defined.

Variant BuiltinFn : Set :=
| Bin_alloca
| Bin_alloca_with_align
| Bin_expect
| Bin_unreachable
| Bin_trap
| Bin_bswap16
| Bin_bswap32
| Bin_bswap64
| Bin_bswap128
| Bin_bzero
| Bin_ffs
| Bin_ffsl
| Bin_ffsll
| Bin_clz
| Bin_clzl
| Bin_clzll
| Bin_ctz
| Bin_ctzl
| Bin_ctzll
| Bin_popcount
| Bin_popcountl
| Bin_unknown (_ : bs)
.
Instance: EqDecision BuiltinFn.
Proof. solve_decision. Defined.

Variant call_type : Set := Virtual | Direct.
Instance: EqDecision call_type.
Proof. solve_decision. Defined.

Inductive Expr : Set :=
| Econst_ref (_ : VarRef) (_ : type)
  (* ^ these are different because they do not have addresses *)
| Evar     (_ : VarRef) (_ : type)
  (* ^ local variable reference *)

| Echar    (_ : Z) (_ : type)
| Estring  (_ : bytestring.bs) (_ : type)
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
| Emember_call (method : (obj_name * call_type) + Expr) (obj : Expr) (_ : list (ValCat * Expr)) (_ : type)
(* ^ in (globname * bool), bool = true when method being called is virtual *)

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

| Ebuiltin (_ : BuiltinFn) (_ : type)
| Eatomic (_ : AtomicOp) (_ : list (ValCat * Expr)) (_ : type)
| Eva_arg (_ : Expr) (_ : type)
| Epseudo_destructor (_ : type) (_ : Expr) (* type void *)
| Eunsupported (_ : bs) (_ : type).
Instance: EqDecision Expr.
Proof.
  do 2 red.
  fix IHe 1.
  decide equality; try solve_trivial_decision.
  all: try eapply list_eq_dec; try solve_trivial_decision.
  all: try eapply prod_eq_dec; try solve_trivial_decision.
  all: try eapply sum_eq_dec; try solve_trivial_decision.
  all: try eapply option_eq_dec; try solve_trivial_decision.
  Unshelve.
  all: try eapply prod_eq_dec; do 2 red; apply IHe.
  Unshelve.
  all: do 2 red; apply IHe.
Defined.

Definition Edefault_init_expr (e : Expr) : Expr := e.
