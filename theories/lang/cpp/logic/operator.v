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

  (** Skeleton for [Beq] and [Bneq] axioms on pointers.

   This specification follows the C++ standard
   (https://eel.is/c++draft/expr.eq#3), and is inspired by Cerberus's pointer
   provenance semantics for C, and Krebbers's thesis. We forbid cases where
   comparisons have undefined or unspecified behavior.

   Crucially, all those semantics _allow_ (but do not _require_) compilers to
   assume that pointers to different objects compare different, even when
   they have the same address. Hence, comparing a past-the-end pointer to an
   object with a pointer to a different object gives unspecified results [1];
   we choose not to support this case.

   - We forbid comparing invalid pointer values; hence, we require
     [p1] and [p2] to satisfy both [_valid_ptr] and [live_ptr].
   - Past-the-end pointers cannot be compared with pointers to the "beginning" of a different object.
     Hence, they can be compared:
     - like Krebbers, with pointers to the same array; more in general, with
       any pointers with the same allocation ID ([same_alloc]).
     - unlike Krebbers, with [nullptr],
       and any pointer [p] not to the beginning of a complete object, per [non_beginning_ptr].
   - In particular, non-past-the-end pointers (including past-the-end
     pointers) can be compared with arbitrary other non-past-the-end pointers.

   [1] From https://eel.is/c++draft/expr.eq#3.1:
   > If one pointer represents the address of a complete object, and another
     pointer represents the address one past the last element of a different
     complete object, the result of the comparison is unspecified.
   *)
  Definition non_beginning_ptr p' : mpred :=
    ∃ p o, [| p' = p .., o /\ ~same_address p p' |]%ptr ∧ valid_ptr p.

  Let comparable strict1 p2 : mpred := [| strict1 = true \/ p2 = nullptr |] ∨ non_beginning_ptr p2.
  Let eval_ptr_eq_cmp_op (bo : BinOp) (t f : Z) : Prop :=
    forall ty p1 p2 strict1 strict2,
      ([| same_alloc p1 p2 |] ∨ (comparable strict1 p2 ∧ comparable strict2 p1)) ∧
      _valid_ptr strict1 p1 ∧ _valid_ptr strict2 p2 ∧ live_ptr p1 ∧ live_ptr p2 ⊢
      eval_binop bo
        (Tpointer ty) (Tpointer ty) Tbool
        (Vptr p1) (Vptr p2) (Vint (if decide (same_address p1 p2) then t else f)) ∗ True.

  Axiom eval_ptr_eq :
    Unfold eval_ptr_eq_cmp_op (eval_ptr_eq_cmp_op Beq 1 0).
  Axiom eval_ptr_neq :
    Unfold eval_ptr_eq_cmp_op (eval_ptr_eq_cmp_op Bneq 0 1).

  (** Skeleton for [Ble, Blt, Bge, Bgt] axioms on pointers. *)
  Let eval_ptr_ord_cmp_op (bo : BinOp) (f : vaddr -> vaddr -> bool) : Prop :=
    forall ty p1 p2 aid res,
      ptr_alloc_id p1 = Some aid ->
      ptr_alloc_id p2 = Some aid ->
      liftM2 f (ptr_vaddr p1) (ptr_vaddr p2) = Some res ->
      (* we could ask [live_ptr p1] or [live_ptr p2], but those are
      equivalent, so we make the statement obviously symmetric. *)
      live_alloc_id aid ⊢
      eval_binop bo
        (Tpointer ty) (Tpointer ty) Tbool
        (Vptr p1) (Vptr p2) (Vbool res) ∗ True.

  Axiom eval_ptr_le :
    Unfold eval_ptr_ord_cmp_op (eval_ptr_ord_cmp_op Ble N.leb).
  Axiom eval_ptr_lt :
    Unfold eval_ptr_ord_cmp_op (eval_ptr_ord_cmp_op Blt N.ltb).
  Axiom eval_ptr_ge :
    Unfold eval_ptr_ord_cmp_op (eval_ptr_ord_cmp_op Bge (fun x y => y <=? x)%N).
  Axiom eval_ptr_gt :
    Unfold eval_ptr_ord_cmp_op (eval_ptr_ord_cmp_op Bgt (fun x y => y <? x)%N).

  (** For non-comparison operations, we do not require liveness, unlike Krebbers.
  We require validity of the result to prevent over/underflow.
  (This is because we don't do pointer zapping, following Cerberus).
  Supporting pointer zapping would require adding [live_ptr] preconditions to
  these operators.
  https://eel.is/c++draft/basic.compound#3.1 *)

  (** Skeletons for ptr/int operators. *)

  Let eval_ptr_int_op (bo : BinOp) (f : Z -> Z) : Prop :=
    forall resolve t w s p1 p2 o ty,
      is_Some (size_of resolve t) ->
      (p2 = p1 .., o_sub resolve ty (f o))%ptr ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop bo
                (Tpointer t) (Tint w s) (Tpointer t)
                (Vptr p1)    (Vint o)  (Vptr p2).

  Let eval_int_ptr_op (bo : BinOp) (f : Z -> Z) : Prop :=
    forall resolve t w s p1 p2 o ty,
      is_Some (size_of resolve t) ->
      (p2 = p1 .., o_sub resolve ty (f o))%ptr ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop bo
                (Tint w s) (Tpointer t) (Tpointer t)
                (Vint o)   (Vptr p1)    (Vptr p2).

  (**
  lhs + rhs (https://eel.is/c++draft/expr.add#1): one of rhs or lhs is a
  pointer to a completely-defined object type
  (https://eel.is/c++draft/basic.types#general-5), the other has integral or
  unscoped enumeration type. In this case, the result type has the type of
  the pointer.

  Liveness note: when adding int [i] to pointer [p], the standard demands
  that [p] points to an array (https://eel.is/c++draft/expr.add#4.2),
  With https://eel.is/c++draft/basic.compound#3.1 and
  https://eel.is/c++draft/basic.memobj#basic.stc.general-4, that implies that
  [p] has not been deallocated.
   *)
  Axiom eval_ptr_int_add :
    Unfold eval_ptr_int_op (eval_ptr_int_op Badd (fun x => x)).

  Axiom eval_int_ptr_add :
    Unfold eval_int_ptr_op (eval_int_ptr_op Badd (fun x => x)).

  (**
  lhs - rhs (https://eel.is/c++draft/expr.add#2.3): lhs is a pointer to
  completely-defined object type
  (https://eel.is/c++draft/basic.types#general-5), rhs has integral or
  unscoped enumeration type. In this case, the result type has the type of
  the pointer.
  Liveness note: as above (https://eel.is/c++draft/expr.add#4).
  *)
  Axiom eval_ptr_int_sub :
    Unfold eval_ptr_int_op (eval_ptr_int_op Bsub Z.opp).

  (**
  lhs - rhs (https://eel.is/c++draft/expr.add#2.2): both lhs and rhs must be
  pointers to the same completely-defined object types
  (https://eel.is/c++draft/basic.types#general-5).
  Liveness note: as above (https://eel.is/c++draft/expr.add#5.2).
  *)
  Axiom eval_ptr_ptr_sub :
    forall resolve t w p1 p2 o1 o2 base ty,
      is_Some (size_of resolve t) ->
      (p1 = base .., o_sub resolve ty o1)%ptr ->
      (p2 = base .., o_sub resolve ty o2)%ptr ->
      (* Side condition to prevent overflow; needed per https://eel.is/c++draft/expr.add#note-1 *)
      has_type (Vint (o1 - o2)) (Tint w Signed) ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop Bsub
                (Tpointer t) (Tpointer t) (Tint w Signed)
                (Vptr p1)    (Vptr p2)    (Vint (o1 - o2)).


End with_Σ.
