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

  (** * Pointer comparison operators *)

  (* Need both ptr_live p1 and ptr_live p2 in general; they coincide for pointers into the same object. *)
  Definition eval_ptr_eq_cmp_op (bo : BinOp) (t f : Z) : Prop :=
    forall ty p1 p2 strict,
      strict = true \/ ptr_alloc_id p1 = ptr_alloc_id p2 ->
      ptr_live p1 ∧ ptr_live p2 ∧ _valid_ptr strict p1 ∧ _valid_ptr strict p2 ⊢
      eval_binop bo (Tpointer ty) (Tpointer ty) Tbool
        (Vptr p1) (Vptr p2) (Vint (if decide (same_address p1 p2) then t else f)) ∗
        (ptr_live p1 ∧ ptr_live p2).

  Axiom eval_ptr_eq :
    Unfold eval_ptr_eq_cmp_op (eval_ptr_eq_cmp_op Beq 1 0).
  Axiom eval_ptr_neq :
    Unfold eval_ptr_eq_cmp_op (eval_ptr_eq_cmp_op Bneq 0 1).

  Definition eval_ptr_ord_cmp_op (bo : BinOp) (t f : Z) : Prop :=
    forall ty p1 p2 aid,
      ptr_alloc_id p1 = Some aid ->
      ptr_alloc_id p2 = Some aid ->
      alloc_id_live aid ⊢
      eval_binop bo (Tpointer ty) (Tpointer ty) Tbool
        (Vptr p1) (Vptr p2) (Vint (if decide (same_address p1 p2) then t else f)) ∗
        alloc_id_live aid.

  (* For operations that aren't comparisons, we don't require liveness, unlike Krebbers. *)
  Definition eval_ptr_int_op (bo : BinOp) (f : Z -> Z) : Prop :=
    forall resolve t w s p1 p2 o ty,
      is_Some (size_of resolve t) ->
      (p2 = p1 .., o_sub resolve ty (f o))%ptr ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop bo
                (Tpointer t) (Tint w s) (Tpointer t)
                (Vptr p1)     (Vint o)  (Vptr p2).

  (* lhs + rhs: one of rhs or lhs is a pointer to completely-defined object type,
    the other has integral or unscoped enumeration type. In this case,
    the result type has the type of the pointer. (rhs has a pointer type) *)
  Axiom eval_ptr_int_add :
    Unfold eval_ptr_int_op (eval_ptr_int_op Badd (fun x => x)).

  (* lhs - rhs: lhs is a pointer to completely-defined object type, rhs
    has integral or unscoped enumeration type. In this case, the result
    type has the type of the pointer. *)
  Axiom eval_ptr_int_sub :
    Unfold eval_ptr_int_op (eval_ptr_int_op Bsub Z.opp).

  Definition eval_int_ptr_op (bo : BinOp) (f : Z -> Z) : Prop :=
    forall resolve t w s p1 p2 o ty,
      is_Some (size_of resolve t) ->
      (p2 = p1 .., o_sub resolve ty (f o))%ptr ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop bo
                (Tint w s) (Tpointer t) (Tpointer t)
                (Vint o)   (Vptr p1)    (Vptr p2).

  (* lhs + rhs: one of rhs or lhs is a pointer to completely-defined object type,
    the other has integral or unscoped enumeration type. In this case,
    the result type has the type of the pointer. (lhs has a pointer type) *)
  Axiom eval_int_ptr_add :
    Unfold eval_int_ptr_op (eval_int_ptr_op Badd (fun x => x)).

  (* lhs - rhs: both lhs and rhs must be pointers to the same
    completely-defined object types. *)
  Axiom eval_ptr_ptr_sub :
    forall resolve t w p1 p2 o1 o2 base ty,
      is_Some (size_of resolve t) ->
      (p1 = base .., o_sub resolve ty o1)%ptr ->
      (p2 = base .., o_sub resolve ty o2)%ptr ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop Bsub
                (Tpointer t) (Tpointer t) (Tint w Signed)
                (Vptr p1)    (Vptr p2)    (Vint (o1 - o2)).


End with_Σ.
