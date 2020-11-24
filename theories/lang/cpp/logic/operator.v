(*
 * Copyright (C) BedRock Systems Inc. 2019-2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.prelude.base.
From bedrock.lang.cpp Require Import ast semantics.values semantics.operator.
From bedrock.lang.cpp Require Import logic.pred.

(* Pointer comparison operators *)

Axiom eval_ptr_eq :
  forall resolve ty a b av bv c,
    a = Vptr av ->
    b = Vptr bv ->
    c = (if ptr_eq_dec av bv then 1 else 0)%Z ->
    eval_binop_pure (resolve:=resolve) Beq (Tpointer ty) (Tpointer ty) Tbool a b (Vint c).
Axiom eval_ptr_neq :
  forall resolve ty a b av bv c,
    a = Vptr av ->
    b = Vptr bv ->
    c = (if ptr_eq_dec av bv then 0 else 1)%Z ->
    eval_binop_pure (resolve:=resolve) Bneq (Tpointer ty) (Tpointer ty) Tbool a b (Vint c).

Definition eval_ptr_int_op (bo : BinOp) (f : Z -> Z) : Prop :=
  forall resolve t w s p o p' sz,
    size_of resolve t = Some sz ->
    p' = offset_ptr_ (f o * Z.of_N sz) p ->
    eval_binop_pure (resolve:=resolve) bo
               (Tpointer t) (Tint w s) (Tpointer t)
               (Vptr p)     (Vint o)   (Vptr p').

(* lhs + rhs: one of rhs or lhs is a pointer to completely-defined object type,
   the other has integral or unscoped enumeration type. In this case,
   the result type has the type of the pointer. (rhs has a pointer type) *)
Axiom eval_ptr_int_add :
  ltac:(let x := eval hnf in (eval_ptr_int_op Badd (fun x => x)) in refine x).

(* lhs - rhs: lhs is a pointer to completely-defined object type, rhs
   has integral or unscoped enumeration type. In this case, the result
   type has the type of the pointer. *)
Axiom eval_ptr_int_sub :
  ltac:(let x := eval hnf in (eval_ptr_int_op Bsub (fun x => -x)%Z) in refine x).

Definition eval_int_ptr_op (bo : BinOp) (f : Z -> Z) : Prop :=
  forall resolve t w s p o p' sz,
    size_of resolve t = Some sz ->
    p' = offset_ptr_ (f o * Z.of_N sz) p ->
    eval_binop_pure (resolve:=resolve) bo
               (Tint w s) (Tpointer t) (Tpointer t)
               (Vint o)   (Vptr p)     (Vptr p').

(* lhs + rhs: one of rhs or lhs is a pointer to completely-defined object type,
   the other has integral or unscoped enumeration type. In this case,
   the result type has the type of the pointer. (lhs has a pointer type) *)
Axiom eval_int_ptr_add :
  ltac:(let x := eval hnf in (eval_int_ptr_op Badd (fun x => x)) in refine x).

(* lhs - rhs: both lhs and rhs must be pointers to the same
   completely-defined object types. *)
Axiom eval_ptr_ptr_sub :
  forall resolve t w p o1 o2 p' base sz,
    size_of resolve t = Some sz ->
    p = offset_ptr_ (Z.of_N sz * o1) base ->
    p' = offset_ptr_ (Z.of_N sz * o2) base ->
    eval_binop_pure (resolve:=resolve) Bsub
               (Tpointer t) (Tpointer t) (Tint w Signed)
               (Vptr p)     (Vptr p')    (Vint (o1 - o2)).
