(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * Semantics of arithmetic and pointer operators.
 *)

(* Note, the syntax tree provides explicit nodes for integral promotion so this file
 * only describes the semantics of operators on uniform types. The one exception is
 * pointer operations (e.g. ptr + int) because that can not be made uniform.
 *)

Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.Ascii.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Semantics.

(* operator semantics *)
Parameter eval_unop : forall {resolve : genv}, UnOp -> forall (argT resT : type) (arg res : val), Prop.
Parameter eval_binop : forall {resolve : genv}, BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), Prop.

Axiom eval_not_bool : forall resolve a,
    eval_unop (resolve:=resolve) Unot Tbool Tbool (Vbool a) (Vbool (negb a)).

(* The builtin unary minus operator calculates the negative of its
   promoted operand. For unsigned a, the value of -a is 2^b -a, where b
   is the number of bits after promotion.  *)
Axiom eval_minus_int : forall resolve s a c w bytes,
    size_of resolve (Tint w s) bytes ->
    c = (if s then (0 - a) else trim (N_of_size w) (0 - a))%Z ->
    has_type (Vint c) (Tint w s) ->
    eval_unop (resolve:=resolve) Uminus (Tint w s) (Tint w s)
              (Vint a) (Vint c).

Definition eval_ptr_int_op (bo : BinOp) (f : Z -> Z) : Prop :=
  forall resolve t w s p o p' sz,
    size_of resolve t sz ->
    p' = offset_ptr_ p (f o * Z.of_N sz) ->
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
    size_of resolve t sz ->
    p' = offset_ptr_ p (f o * Z.of_N sz) ->
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
    size_of resolve t sz ->
    p = offset_ptr_ base (Z.of_N sz * o1) ->
    p' = offset_ptr_ base (Z.of_N sz * o2) ->
    eval_binop (resolve:=resolve) Bsub
               (Tpointer t) (Tpointer t) (Tint w Signed)
               (Vptr p)     (Vptr p')    (Vint (o1 - o2)).

Definition eval_int_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall resolve w (s : signed) (a b c : Z),
    c = (if s then o a b else trim (N_of_size w) (o a b)) ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

Definition eval_int_bin_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall resolve w (s : signed) (a b c : Z),
    c = (if s then o a b else trim (N_of_size w) (o a b)) ->
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
  ltac:(let x := eval hnf in (eval_int_op Bor Z.lor) in refine x).
Axiom eval_and :
  ltac:(let x := eval hnf in (eval_int_op Band Z.land) in refine x).
Axiom eval_xor :
  ltac:(let x := eval hnf in (eval_int_op Bxor Z.lxor) in refine x).

(* The binary operator / divides the first operand by the second, after usual
   arithmetic conversions.
   The quotient is truncated towards zero (fractional part is discarded),
   since C++11.
   If the second operand is zero, the behavior is undefined. *)
Axiom eval_div :
  forall resolve (w : size) (s : signed) (a b c : Z),
    b <> 0%Z ->
    c = Z.quot a b ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) Bdiv (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).
Axiom eval_mod :
  forall resolve (w : size) (s : signed) (a b c : Z),
    b <> 0%Z ->
    c = Z.rem a b ->
    has_type (Vint c) (Tint w s) ->
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
   operand.  *)
Axiom eval_shl :
  forall resolve (w : size) (s : signed) (a b c : Z),
    (0 <= b < Z_of_size w)%Z ->
    (0 <= a)%Z ->
    (c = if s then Z.shiftl a b else trim (N_of_size w) (Z.shiftl a b)) ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) Bshl (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* [C++14,C++20): The value of E1 >> E2 is E1 right-shifted E2 bit
   positions. If E1 has an unsigned type or if E1 has a signed type
   and a non-negative value, the value of the result is the integral
   part of the quotient of E1/(2^E2). If E1 has a signed type and a
   negative value, the resulting value is implementation-defined. *)
Axiom eval_shr :
  forall resolve (w : size) (s : signed) (a b c : Z),
    (0 <= b < Z_of_size w)%Z ->
    (0 <= a)%Z ->
    (c = if s then Z.shiftr a b else trim (N_of_size w) (Z.shiftr a b)) ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) Bshr (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

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
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) Tbool a b (Vint c).

Definition eval_int_rel_op_int (bo : BinOp) {P Q : Z -> Z -> Prop}
           (o : forall a b : Z, {P a b} + {Q a b}) : Prop :=
  forall resolve w s a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) (T_int) a b (Vint c).

Axiom eval_eq_bool :
  ltac:(let x := eval hnf in (eval_int_rel_op Beq Z.eq_dec) in refine x).
Axiom eval_neq_bool :
  forall resolve ty a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
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
