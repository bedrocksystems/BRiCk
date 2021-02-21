(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.tactics.
From iris_string_ident Require Import ltac2_string_ident.
From bedrock.lang.prelude Require Import base option.
From bedrock.lang.cpp Require Import ast semantics.values semantics.operator.
From bedrock.lang.cpp Require Import logic.pred.

Parameter eval_binop_impure : forall `{has_cpp : cpp_logic} {resolve : genv}, BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), mpred.

(** Pointer [p'] is not at the beginning of a block. *)
Definition non_beginning_ptr `{has_cpp : cpp_logic} p' : mpred :=
  ∃ p o, [| p' = p .., o /\
    (* ensure that o is > 0 *)
    some_Forall2 N.lt (ptr_vaddr p) (ptr_vaddr p') |] ∧ valid_ptr p.

Section non_beginning_ptr.
  Context `{has_cpp : cpp_logic}.

  #[global] Instance non_beginning_ptr_persistent p : Persistent (non_beginning_ptr p) := _.
  #[global] Instance non_beginning_ptr_affine p : Affine (non_beginning_ptr p) := _.
  #[global] Instance non_beginning_ptr_timeless p : Timeless (non_beginning_ptr p) := _.
End non_beginning_ptr.

Typeclasses Opaque non_beginning_ptr.

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
   As a deviation, we assume compilers do not perform lifetime-end pointer
   zapping (see http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2443.pdf).

   Crucially, all those semantics _allow_ (but do not _require_) compilers to
   assume that pointers with distinct provenances compare different, even when
   they have the same address.

   - Hence, comparing a past-the-end pointer to an object with a pointer to a
     different object gives unspecified results [1]; we choose not to support
     this case.
   - We make assumptions about pointer validity.
     A dangling pointer and a non-null live pointer have different
     provenances but can have the same address.
     As we don't support pointer zapping, we assume dangling pointers can be reliably
     distinguished from [nullptr]. Hence, we require pointers under
     comparison [p1] and [p2] to satisfy [live_ptr_if_needed] but not
     [live_ptr].
     We also require [p1] and [p2] to satisfy [_valid_ptr], even for comparisons against [nullptr].
     Hence, null pointers can be compared with pointers satisfying [valid_ptr],
     and otherwise we require that neither [p1] nor [p2] is an "invalid
     pointer values" in the C++ sense (see [_valid_ptr] for discussion).

   - Via [ptr_unambiguous_cmp], we forbid comparing a one-past-the-end
     pointer to an object with a pointer to the "beginning" of a different
     object.
     Hence, past-the-end pointers can be compared:
     - like Krebbers, with pointers to the same array; more in general, with
       any pointers with the same allocation ID ([same_alloc]).
     - unlike Krebbers, with [nullptr], and any pointer [p] not to the
       beginning of a complete object, per [non_beginning_ptr].
     In particular, non-past-the-end pointers can be compared with arbitrary
     other non-past-the-end pointers.

   [1] From https://eel.is/c++draft/expr.eq#3.1:
   > If one pointer represents the address of a complete object, and another
     pointer represents the address one past the last element of a different
     complete object, the result of the comparison is unspecified.
   *)
  #[local] Definition ptr_unambiguous_cmp vt1 p2 : mpred := (* affine *)
    [| p2 = nullptr |] ∨ [| vt1 = Strict |] ∨ non_beginning_ptr p2.
  Lemma ptr_unambiguous_cmp_nullptr vt : ⊢ ptr_unambiguous_cmp vt nullptr.
  Proof. rewrite /ptr_unambiguous_cmp; iLeft; eauto. Qed.
  Lemma ptr_unambiguous_cmp_other_strict p : ⊢ ptr_unambiguous_cmp Strict p.
  Proof. rewrite /ptr_unambiguous_cmp; eauto. Qed.

  #[local] Definition live_ptr_if_needed p1 p2 : mpred := (* ownership *)
    live_ptr p1 ∨ [| p2 = nullptr |].
  Lemma live_ptr_if_needed_1 p : ⊢ live_ptr_if_needed p nullptr.
  Proof. rewrite /live_ptr_if_needed; eauto. Qed.
  Lemma live_ptr_if_needed_2 p : ⊢ live_ptr_if_needed nullptr p.
  Proof. rewrite /live_ptr_if_needed -nullptr_live; eauto. Qed.

  (** Can these pointers be validly compared? *)
  (* Written to ease showing [ptr_comparable_symm]. *)
  Definition ptr_comparable p1 p2 vt1 vt2 res : mpred :=
    (* These premises let you assume that that [p1] and [p2] have an address. *)
    [| is_Some (ptr_vaddr p1) /\ is_Some (ptr_vaddr p2) |] -∗
    [| same_address_bool p1 p2 = res |] ∗
    ([| same_alloc p1 p2 |] ∨ (ptr_unambiguous_cmp vt1 p2 ∧ ptr_unambiguous_cmp vt2 p1)) ∗
    (_valid_ptr vt1 p1 ∧ _valid_ptr vt2 p2) ∗
    (live_ptr_if_needed p1 p2 ∧ live_ptr_if_needed p2 p1).

  Lemma ptr_comparable_symm p1 p2 vt1 vt2 res :
    ptr_comparable p1 p2 vt1 vt2 res ⊢ ptr_comparable p2 p1 vt2 vt1 res.
  Proof.
    (* To ease rearranging conjuncts or changing connectives, we repeat the
    body (which is easy to update), not the nesting structure. *)
    rewrite {2}/ptr_comparable.
    rewrite !(comm and (is_Some (ptr_vaddr p2)), comm same_address_bool p2, comm same_alloc p2,
      comm _ (ptr_unambiguous_cmp vt2 _), comm _ (_valid_ptr vt2 _), comm _ (live_ptr_if_needed p2 _)).
    rewrite /ptr_comparable. repeat f_equiv.
  Qed.

  Lemma nullptr_ptr_comparable {p res} :
    (is_Some (ptr_vaddr p) -> bool_decide (p = nullptr) = res) ->
    valid_ptr p ⊢ ptr_comparable p nullptr Relaxed Strict res.
  Proof.
    iIntros "%HresI V" ([Haddr _]).
    iDestruct (same_address_bool_null with "V") as %->. iFrame "V".
    move: Haddr => {}/HresI Hres. iFrame (Hres).
    rewrite -strict_valid_ptr_nullptr.
    rewrite -live_ptr_if_needed_1 -live_ptr_if_needed_2.
    rewrite -ptr_unambiguous_cmp_nullptr -ptr_unambiguous_cmp_other_strict.
    rewrite !(right_id emp%I). by iRight.
  Qed.

  Lemma self_ptr_comparable p :
    valid_live_ptr p ⊢ ptr_comparable p p Relaxed Relaxed true.
  Proof.
    iIntros "[#V L]" ([_ Haddr]). have Hsame := (same_address_bool_partial_reflexive _ Haddr).
    iDestruct (same_alloc_refl with "V") as "$". iFrame (Hsame) "V L".
  Qed.

  #[local] Definition eval_ptr_eq_cmp_op (bo : BinOp) ty p1 p2 res : mpred :=
    eval_binop_impure bo
      (Tpointer ty) (Tpointer ty) Tbool
      (Vptr p1) (Vptr p2) (Vbool res) ∗ True.

  Axiom eval_ptr_eq : forall vt1 vt2 ty p1 p2 res,
      ptr_comparable p1 p2 vt1 vt2 res
    ⊢ Unfold eval_ptr_eq_cmp_op (eval_ptr_eq_cmp_op Beq ty p1 p2 res).

  Lemma eval_ptr_nullptr_eq_l {ty vp res} :
    (is_Some (ptr_vaddr vp) -> bool_decide (vp = nullptr) = res) ->
    valid_ptr vp ⊢ Unfold eval_ptr_eq_cmp_op (eval_ptr_eq_cmp_op Beq ty vp nullptr res).
  Proof. intros ->%nullptr_ptr_comparable. by rewrite -eval_ptr_eq. Qed.

  Lemma eval_ptr_nullptr_eq_r {ty vp res} :
    (is_Some (ptr_vaddr vp) -> bool_decide (vp = nullptr) = res) ->
    valid_ptr vp ⊢ Unfold eval_ptr_eq_cmp_op (eval_ptr_eq_cmp_op Beq ty nullptr vp res).
  Proof. intros ->%nullptr_ptr_comparable. by rewrite ptr_comparable_symm -eval_ptr_eq. Qed.

  Lemma eval_ptr_self_eq ty p :
    valid_live_ptr p ⊢ Unfold eval_ptr_eq_cmp_op (eval_ptr_eq_cmp_op Beq ty p p true).
  Proof. by rewrite -(eval_ptr_eq Relaxed Relaxed) -self_ptr_comparable. Qed.

  Axiom eval_ptr_neq : forall ty p1 p2 res,
    Unfold eval_ptr_eq_cmp_op
      (eval_ptr_eq_cmp_op Beq ty p1 p2 res
    ⊢ eval_ptr_eq_cmp_op Bneq ty p1 p2 (negb res)).

  (** Skeleton for [Ble, Blt, Bge, Bgt] axioms on pointers. *)
  #[local] Definition eval_ptr_ord_cmp_op (bo : BinOp) (f : vaddr -> vaddr -> bool) : Prop :=
    forall ty p1 p2 aid res,
      ptr_alloc_id p1 = Some aid ->
      ptr_alloc_id p2 = Some aid ->
      (is_Some (ptr_vaddr p1) -> is_Some (ptr_vaddr p2) -> liftM2 f (ptr_vaddr p1) (ptr_vaddr p2) = Some res) ->

      valid_ptr p1 ∧ valid_ptr p2 ∧
      (* we could ask [live_ptr p1] or [live_ptr p2], but those are
      equivalent, so we make the statement obviously symmetric. *)
      live_alloc_id aid ⊢
      eval_binop_impure bo
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

  #[local] Definition eval_ptr_int_op (bo : BinOp) (f : Z -> Z) : Prop :=
    forall w s p1 p2 o ty,
      is_Some (size_of resolve ty) ->
      p2 = p1 .., _sub ty (f o) ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop_impure bo
                (Tpointer ty) (Tint w s) (Tpointer ty)
                (Vptr p1)     (Vint o)   (Vptr p2).

  #[local] Definition eval_int_ptr_op (bo : BinOp) (f : Z -> Z) : Prop :=
    forall w s p1 p2 o ty,
      is_Some (size_of resolve ty) ->
      p2 = p1 .., _sub ty (f o) ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop_impure bo
                (Tint w s) (Tpointer ty) (Tpointer ty)
                (Vint o)   (Vptr p1)     (Vptr p2).

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
    forall w p1 p2 o1 o2 base ty,
      is_Some (size_of resolve ty) ->
      p1 = base .., _sub ty o1 ->
      p2 = base .., _sub ty o2 ->
      (* Side condition to prevent overflow; needed per https://eel.is/c++draft/expr.add#note-1 *)
      has_type (Vint (o1 - o2)) (Tint w Signed) ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      eval_binop_impure Bsub
                (Tpointer ty) (Tpointer ty) (Tint w Signed)
                (Vptr p1)     (Vptr p2)     (Vint (o1 - o2)).
End with_Σ.
