(*
 * Copyright (C) BedRock Systems Inc. 2019-2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.prelude.base.
From bedrock.lang.cpp Require Import ast semantics.values semantics.operator.
From bedrock.lang.cpp Require Import logic.pred.

Parameter eval_binop_impure : forall `{has_cpp : cpp_logic} {resolve : genv}, BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), mpred.
Section with_Σ.
  Context `{has_cpp : cpp_logic} {resolve : genv}.
  Notation eval_binop_pure := (eval_binop_pure (resolve := resolve)).
  Notation eval_binop_impure := (eval_binop_impure (resolve := resolve)).

  Definition eval_binop (b : BinOp) (lhsT rhsT resT : type) (lhs rhs res : val) : mpred :=
    [| eval_binop_pure b lhsT rhsT resT lhs rhs res |] ∨ eval_binop_impure b lhsT rhsT resT lhs rhs res.

(* TODO make linear. *)
Definition ptr_eq_cmpable p : mpred :=
  (<absorb> [| p = nullptr |]) ∨ (ptr_live p ∧ strict_valid_ptr p).

(* TODO make linear. *)
(* TODO: need both ptr_live p1 and ptr_live p2? *)
Definition ptr_subtraction_possible σ ty p1 p2 : mpred :=
  [| ∃ p n1 n2, p1 = p .., o_sub σ ty n1 /\ p2 = p .., o_sub σ ty n2 |]%ptr ∧
  valid_ptr p1 ∧ valid_ptr p2 ∧ ptr_live p1 ∧ ptr_live p2.

(* TODO make linear. *)
(** * Pointer comparison operators *)
Axiom eval_ptr_eq :
  forall σ ty a b av bv c,
    a = Vptr av ->
    b = Vptr bv ->
    c = (if decide (same_address av bv) then 1 else 0)%Z ->
    (ptr_eq_cmpable av ∧ ptr_eq_cmpable bv) ∨ ptr_subtraction_possible σ ty av bv ⊢
    eval_binop Beq (Tpointer ty) (Tpointer ty) Tbool a b (Vint c).

Axiom eval_ptr_neq :
  forall σ ty a b av bv c,
    a = Vptr av ->
    b = Vptr bv ->
    c = (if decide (same_address av bv) then 0 else 1)%Z ->
    (ptr_eq_cmpable av ∧ ptr_eq_cmpable bv) ∨ ptr_subtraction_possible σ ty av bv ⊢
    eval_binop Bneq (Tpointer ty) (Tpointer ty) Tbool a b (Vint c).

Definition eval_ptr_int_op (bo : BinOp) (f : Z -> Z) : Prop :=
  forall resolve t w s p o p' sz,
    size_of resolve t = Some sz ->
    p' = offset_ptr_ (f o * Z.of_N sz) p ->
    |-- eval_binop bo
               (Tpointer t) (Tint w s) (Tpointer t)
               (Vptr p)     (Vint o)   (Vptr p').

(* lhs + rhs: one of rhs or lhs is a pointer to completely-defined object type,
   the other has integral or unscoped enumeration type. In this case,
   the result type has the type of the pointer. (rhs has a pointer type) *)
Axiom eval_ptr_int_add :
  Unfold eval_ptr_int_op (eval_ptr_int_op Badd (fun x => x)).

(* lhs - rhs: lhs is a pointer to completely-defined object type, rhs
   has integral or unscoped enumeration type. In this case, the result
   type has the type of the pointer. *)
Axiom eval_ptr_int_sub :
  Unfold eval_ptr_int_op (eval_ptr_int_op Bsub (fun x => -x)%Z).

Definition eval_int_ptr_op (bo : BinOp) (f : Z -> Z) : Prop :=
  forall resolve t w s p o p' sz,
    size_of resolve t = Some sz ->
    p' = offset_ptr_ (f o * Z.of_N sz) p ->
    |-- eval_binop bo
               (Tint w s) (Tpointer t) (Tpointer t)
               (Vint o)   (Vptr p)     (Vptr p').

(* lhs + rhs: one of rhs or lhs is a pointer to completely-defined object type,
   the other has integral or unscoped enumeration type. In this case,
   the result type has the type of the pointer. (lhs has a pointer type) *)
Axiom eval_int_ptr_add :
  Unfold eval_int_ptr_op (eval_int_ptr_op Badd (fun x => x)).

(* lhs - rhs: both lhs and rhs must be pointers to the same
   completely-defined object types. *)
Axiom eval_ptr_ptr_sub :
  forall resolve t w p o1 o2 p' base sz,
    size_of resolve t = Some sz ->
    p = offset_ptr_ (Z.of_N sz * o1) base ->
    p' = offset_ptr_ (Z.of_N sz * o2) base ->
    |-- eval_binop Bsub
               (Tpointer t) (Tpointer t) (Tint w Signed)
               (Vptr p)     (Vptr p')    (Vint (o1 - o2)).

End with_Σ.
