(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(**
 * Semantics of arithmetic and pointer operators.
 *)

(* Note, the syntax tree provides explicit nodes for integral promotion so
 * we only describes the semantics of operators on uniform types. The one
 * exception is pointer operations (e.g. ptr + int) because that can not be
 * made uniform.
 *)

Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.ssr.ssreflect.
Require Import stdpp.decidable.
From bedrock.lang.cpp Require Import ast semantics.values.

Local Open Scope Z_scope.
Local Open Scope general_if_scope.

Set Default Proof Using "Type".

Local Ltac smash __N :=
  generalize dependent __N; intro __N; destruct __N; rewrite /bitsZ /=; try lia.


(** truncation (used for unsigned operations) *)
Definition trim (w : N) (v : Z) : Z :=
  v mod (2 ^ Z.of_N w).

(** [to_unsigned sz z] is used when C++ converts signed values to unsigned
    values.

    "the unique value congruent to [z] modulo [2^sz]
     where [sz] is the number of bits in the return type"
 *)
Definition to_unsigned (sz : N) (z : Z) : Z :=
  trim sz z.

Lemma to_unsigned_id : forall z (sz : N),
    (0 <= z < 2^Z.of_N sz)%Z ->
    to_unsigned sz z = z.
Proof.
  rewrite /to_unsigned /trim.
  intros. rewrite Z.mod_small; auto.
Qed.

Lemma to_unsigned_neg : forall z (sz : N),
    0 < z ->
    to_unsigned sz z = z mod 2^Z.of_N sz.
Proof. reflexivity. Qed.

(** [to_signed sz z] is used when C++ converts unsigned values to signed values.

    the standard describes it as:

    "the value does not change if the source integer can be represented in the
     destination type. Otherwise the result is,
     - implementation-defined (until C++20)
     - the unique value of the destination type equal to the source value modulo [2^sz]
       where [sz] is the number of bits used to represent the destination type."
 *)
Definition to_signed (sz : bitsize) (z : Z) : Z :=
  let norm := Z.modulo z (2 ^ bitsZ sz) in
  if bool_decide (norm >= 2 ^ (bitsZ sz - 1)) then
    norm - 2 ^ bitsZ sz
  else
    norm.

Local Transparent bitsZ bitsN.
Arguments bitsZ !_.
Arguments Z.of_N !_.
Arguments bitsN !_.

(* lemmas for [to_signed] and [to_unsigned] *)
Lemma to_signed_id : forall (z : Z) (n : bitsize),
  0 <= z < 2^(bitsZ n - 1) -> to_signed n z = z.
Proof.
  intros; rewrite /to_signed Z.mod_small. smash n.
  rewrite bool_decide_eq_false_2; smash n.
Qed.


Lemma to_signed_neg : forall x (n : bitsize),
    2^(bitsZ n - 1) - 1 < x < 2^bitsZ n ->
    to_signed n x = trim (bitsN n) (x - 2^(bitsZ n - 1)) + - 2^(bitsZ n - 1).
Proof.
  clear; intros x n.
  rewrite /to_signed /trim. intros.
  rewrite Z.mod_small. smash n.
  rewrite bool_decide_eq_true_2; [ smash n | ].
  rewrite Z.mod_small; smash n.
Qed.

(** Integral conversions *)
Definition conv_int (from to : type) (v v' : val) : Prop :=
  match drop_qualifiers from , drop_qualifiers to with
  | Tbool , Tint _ _ =>
    match is_true v with
    | Some v => v' = Vbool v
    | _ => False
    end
  | Tint _ _ , Tbool =>
    match v with
    | Vint v =>
      v' = Vbool (if Z.eqb 0 v then false else true)
    | _ => False
    end
  | Tint _ _ , Tint sz Unsigned =>
    match v with
    | Vint v =>
      v' = Vint (to_unsigned (bitsN sz) v)
    | _ => False
    end
  | Tint _ _ , Tint sz Signed =>
    has_type v (Tint sz Signed) /\ v' = v
  | _ , _ => False
  end.


(** operator semantics *)
Parameter eval_unop : forall {resolve : genv}, UnOp -> forall (argT resT : type) (arg res : val), Prop.
Parameter eval_binop : forall {resolve : genv}, BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), Prop.

Axiom eval_not_bool : forall resolve a,
    eval_unop (resolve:=resolve) Unot Tbool Tbool (Vbool a) (Vbool (negb a)).

(* The builtin unary minus operator calculates the negative of its
   promoted operand. For unsigned a, the value of -a is 2^b -a, where b
   is the number of bits after promotion.  *)
Axiom eval_minus_int : forall resolve (s : signed) a c w,
    c = match s with
        | Signed => 0 - a
        | Unsigned => trim (bitsN w) (0 - a)
        end ->
    has_type (Vint c) (Tint w s) ->
    eval_unop (resolve:=resolve) Uminus (Tint w s) (Tint w s)
              (Vint a) (Vint c).

Definition eval_ptr_int_op (bo : BinOp) (f : Z -> Z) : Prop :=
  forall resolve t w s p o p' sz,
    size_of resolve t = Some sz ->
    p' = offset_ptr_ (f o * Z.of_N sz) p ->
    eval_binop (resolve:=resolve) bo
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
    eval_binop (resolve:=resolve) bo
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
    eval_binop (resolve:=resolve) Bsub
               (Tpointer t) (Tpointer t) (Tint w Signed)
               (Vptr p)     (Vptr p')    (Vint (o1 - o2)).

Definition eval_int_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall resolve w (s : signed) (a b c : Z),
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w s) ->
    c = match s with
        | Signed => o a b
        | Unsigned => trim (bitsN w) (o a b)
        end ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* this is bitwise operators *)
Definition eval_int_bitwise_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall resolve w (s : signed) (a b c : Z),
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w s) ->
    c = o a b -> (* note that bitwise operators respect bounds *)
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* arithmetic operators *)
Axiom eval_add :
  ltac:(let x := eval hnf in (eval_int_op Badd Z.add) in refine x).
Axiom eval_sub :
  ltac:(let x := eval hnf in (eval_int_op Bsub Z.sub) in refine x).
Axiom eval_mul :
  ltac:(let x := eval hnf in (eval_int_op Bmul Z.mul) in refine x).

(* bitwise(logical) operators *)
Axiom eval_or :
  ltac:(let x := eval hnf in (eval_int_bitwise_op Bor Z.lor) in refine x).
Axiom eval_and :
  ltac:(let x := eval hnf in (eval_int_bitwise_op Band Z.land) in refine x).
Axiom eval_xor :
  ltac:(let x := eval hnf in (eval_int_bitwise_op Bxor Z.lxor) in refine x).

(* The binary operator / divides the first operand by the second, after usual
   arithmetic conversions.
   The quotient is truncated towards zero (fractional part is discarded),
   since C++11.
   If the second operand is zero, the behavior is undefined. *)
Axiom eval_div :
  forall resolve (w : bitsize) (s : signed) (a b c : Z),
    b <> 0%Z ->
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w s) ->
    c = Z.quot a b ->
    eval_binop (resolve:=resolve) Bdiv (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).
Axiom eval_mod :
  forall resolve (w : bitsize) (s : signed) (a b c : Z),
    b <> 0%Z ->
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w s) ->
    c = Z.rem a b ->
    eval_binop (resolve:=resolve) Bmod (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* [C++14,C++20) *)
(* The value of E1 << E2 is E1 left-shifted E2 bit positions; vacated
   bits are zero-filled. If E1 has an unsigned type, the value of the
   result is E1 * 2^E2, reduced modulo one more than the maximum value
   representable in the result type. Otherwise, if E1 has a signed
   type and non-negative value, and E1 * 2 ^ E2 is representable in
   the corresponding unsigned type of the result type, then that
   value, converted to the result type, is the resulting value;
   otherwise, the behavior is undefined.  *)
(* The behavior is undefined if the right operand is negative, or
   greater than or equal to the length in bits of the promoted left
   operand.
In overload resolution against user-defined operators, for every pair of promoted integral types L and R, the following function signatures participate in overload resolution:

L operator<<(L, R)
L operator>>(L, R)

  *)

Axiom eval_shl :
  forall resolve (w : bitsize) w2 (s s2 : signed) (a b c : Z),
    (0 <= b < bitsZ w)%Z ->
    (0 <= a)%Z ->
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w2 s2) ->
    c = match s with
        | Signed => Z.shiftl a b
        | Unsigned => trim (bitsN w) (Z.shiftl a b)
        end ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) Bshl (Tint w s) (Tint w2 s2) (Tint w s) (Vint a) (Vint b) (Vint c).

(* [C++14,C++20): The value of E1 >> E2 is E1 right-shifted E2 bit
   positions. If E1 has an unsigned type or if E1 has a signed type
   and a non-negative value, the value of the result is the integral
   part of the quotient of E1/(2^E2). If E1 has a signed type and a
   negative value, the resulting value is implementation-defined. *)
Axiom eval_shr :
  forall resolve (w : bitsize) w2 (s s2: signed) (a b c : Z),
    (0 <= b < bitsZ w)%Z ->
    (0 <= a)%Z ->
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w2 s2) ->
    c = match s with Signed => Z.shiftr a b | Unsigned => trim (bitsN w) (Z.shiftr a b) end ->
    eval_binop (resolve:=resolve) Bshr (Tint w s) (Tint w2 s2) (Tint w s) (Vint a) (Vint b) (Vint c).

(* Arithmetic comparison operators *)

(* If the operands has arithmetic or enumeration type (scoped or
   unscoped), usual arithmetic conversions are performed on both
   operands following the rules for arithmetic operators. The values
   are compared after conversions. *)
Definition eval_int_rel_op (bo : BinOp) {P Q : Z -> Z -> Prop}
           (o : forall a b : Z, {P a b} + {Q a b}) : Prop :=
  forall resolve w s a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    has_type a (Tint w s) ->
    has_type b (Tint w s) ->
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) Tbool a b (Vint c).

Definition eval_int_rel_op_int (bo : BinOp) {P Q : Z -> Z -> Prop}
           (o : forall a b : Z, {P a b} + {Q a b}) : Prop :=
  forall resolve w s a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    has_type a (Tint w s) ->
    has_type b (Tint w s) ->
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) (T_int) a b (Vint c).

Axiom eval_eq_bool :
  ltac:(let x := eval hnf in (eval_int_rel_op Beq Z.eq_dec) in refine x).
Axiom eval_neq_bool :
  forall resolve ty a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    has_type a ty ->
    has_type b ty ->
    c = (if Z.eq_dec av bv then 0 else 1)%Z ->
    eval_binop (resolve:=resolve) Bneq ty ty Tbool a b (Vint c).
Axiom eval_lt_bool :
  ltac:(let x := eval hnf in (eval_int_rel_op Blt ZArith_dec.Z_lt_ge_dec) in refine x).
Axiom eval_gt_bool :
  ltac:(let x := eval hnf in (eval_int_rel_op Bgt ZArith_dec.Z_gt_le_dec) in refine x).
Axiom eval_le_bool :
  ltac:(let x := eval hnf in (eval_int_rel_op Ble ZArith_dec.Z_le_gt_dec) in refine x).
Axiom eval_ge_bool :
  ltac:(let x := eval hnf in (eval_int_rel_op Bge ZArith_dec.Z_ge_lt_dec) in refine x).

Axiom eval_eq_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Beq Z.eq_dec) in refine x).
Axiom eval_neq_int :
  forall resolve ty a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if Z.eq_dec av bv then 0 else 1)%Z ->
    eval_binop (resolve:=resolve) Bneq ty ty T_int a b (Vint c).
Axiom eval_lt_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Blt ZArith_dec.Z_lt_ge_dec) in refine x).
Axiom eval_gt_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Bgt ZArith_dec.Z_gt_le_dec) in refine x).
Axiom eval_le_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Ble ZArith_dec.Z_le_gt_dec) in refine x).
Axiom eval_ge_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Bge ZArith_dec.Z_ge_lt_dec) in refine x).

(* Pointer comparison operators *)

Axiom eval_ptr_eq :
  forall resolve ty a b av bv c,
    a = Vptr av ->
    b = Vptr bv ->
    c = (if ptr_eq_dec av bv then 1 else 0)%Z ->
    eval_binop (resolve:=resolve) Beq (Tpointer ty) (Tpointer ty) Tbool a b (Vint c).
Axiom eval_ptr_neq :
  forall resolve ty a b av bv c,
    a = Vptr av ->
    b = Vptr bv ->
    c = (if ptr_eq_dec av bv then 0 else 1)%Z ->
    eval_binop (resolve:=resolve) Bneq (Tpointer ty) (Tpointer ty) Tbool a b (Vint c).

Definition bitFlipZU (len: bitsize) (z:Z) : Z :=
  to_unsigned (bitsN len) (Z.lnot z).

(* note [Z.lnot a = -1 - a] *)
Axiom eval_unop_not:
  forall {genv} (w : bitsize) (sgn : signed) (a b : Z),
    b = match sgn with Signed => -1 - a | Unsigned => bitFlipZU w a end ->
    has_type (Vint b) (Tint w sgn) ->
    @eval_unop genv Ubnot (Tint w sgn) (Tint w sgn)  (Vint a) (Vint b).

(** for pre- and post- increment/decrement, this function determines the type
    of the [1] that is added or subtracted
 *)
Fixpoint companion_type (t : type) : option type :=
  match t with
  | Tpointer _ => Some (Tint int_bits Signed)
  | Tint _ _ => Some t
  | Tqualified _ t => companion_type t
  | _ => None
  end.
