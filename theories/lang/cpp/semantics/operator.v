(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
 * Semantics of arithmetic and pointer operators.
 *)

(* Note, the syntax tree provides explicit nodes for integral promotion so
 * we only describes the semantics of operators on uniform types. The one
 * exception is pointer operations (e.g. ptr + int) because that can not be
 * made uniform.
 *)

From bedrock.prelude Require Import base numbers.
From bedrock.lang.cpp.arith Require Export operator.
From bedrock.lang.cpp Require Import ast semantics.values.

Local Open Scope Z_scope.



(** operator semantics *)
Parameter eval_unop : forall {resolve : genv}, UnOp -> forall (argT resT : type) (arg res : val), Prop.
Parameter eval_binop_pure : forall {resolve : genv}, BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), Prop.


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
      v' = Vint (to_unsigned sz v)
    | _ => False
    end
  | Tint _ _ , Tint sz Signed =>
    has_type v (Tint sz Signed) /\ v' = v
  | _ , _ => False
  end.
Arguments conv_int !_ !_ _ _ /.

#[local] Definition eval_int_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall resolve w (s : signed) (a b c : Z),
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w s) ->
    c = match s with
        | Signed => o a b
        | Unsigned => trim (bitsN w) (o a b)
        end ->
    has_type (Vint c) (Tint w s) ->
    eval_binop_pure (resolve:=resolve) bo (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* this is bitwise operators *)
#[local] Definition eval_int_bitwise_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall resolve w (s : signed) (a b c : Z),
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w s) ->
    c = o a b -> (* note that bitwise operators respect bounds *)
    eval_binop_pure (resolve:=resolve) bo (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* Arithmetic comparison operators *)

(* If the operands has arithmetic or enumeration type (scoped or
   unscoped), usual arithmetic conversions are performed on both
   operands following the rules for arithmetic operators. The values
   are compared after conversions. *)
#[local] Definition eval_int_rel_op (bo : BinOp) {P Q : Z -> Z -> Prop}
           (o : forall a b : Z, {P a b} + {Q a b}) : Prop :=
  forall resolve w s a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    has_type a (Tint w s) ->
    has_type b (Tint w s) ->
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop_pure (resolve:=resolve) bo (Tint w s) (Tint w s) Tbool a b (Vint c).

#[local] Definition eval_int_rel_op_int (bo : BinOp) {P Q : Z -> Z -> Prop}
           (o : forall a b : Z, {P a b} + {Q a b}) : Prop :=
  forall resolve w s a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    has_type a (Tint w s) ->
    has_type b (Tint w s) ->
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop_pure (resolve:=resolve) bo (Tint w s) (Tint w s) (T_int) a b (Vint c).

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

(* arithmetic operators *)
Axiom eval_add : Hnf (eval_int_op Badd Z.add).
Axiom eval_sub : Hnf (eval_int_op Bsub Z.sub).
Axiom eval_mul : Hnf (eval_int_op Bmul Z.mul).

(* bitwise(logical) operators *)
Axiom eval_or : Hnf (eval_int_bitwise_op Bor Z.lor).
Axiom eval_and : Hnf (eval_int_bitwise_op Band Z.land).
Axiom eval_xor : Hnf (eval_int_bitwise_op Bxor Z.lxor).

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
    eval_binop_pure (resolve:=resolve) Bdiv (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).
Axiom eval_mod :
  forall resolve (w : bitsize) (s : signed) (a b c : Z),
    b <> 0%Z ->
    has_type (Vint a) (Tint w s) ->
    has_type (Vint b) (Tint w s) ->
    c = Z.rem a b ->
    eval_binop_pure (resolve:=resolve) Bmod (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* C++14 <= VER < C++20 *)
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
    eval_binop_pure (resolve:=resolve) Bshl (Tint w s) (Tint w2 s2) (Tint w s) (Vint a) (Vint b) (Vint c).

(* C++14 <= VER < C++20: The value of E1 >> E2 is E1 right-shifted E2 bit
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
    eval_binop_pure (resolve:=resolve) Bshr (Tint w s) (Tint w2 s2) (Tint w s) (Vint a) (Vint b) (Vint c).

Axiom eval_eq_bool : Hnf (eval_int_rel_op Beq Z.eq_dec).
Axiom eval_neq_bool :
  forall resolve ty a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    has_type a ty ->
    has_type b ty ->
    c = (if Z.eq_dec av bv then 0 else 1)%Z ->
    eval_binop_pure (resolve:=resolve) Bneq ty ty Tbool a b (Vint c).
Axiom eval_lt_bool : Hnf (eval_int_rel_op Blt ZArith_dec.Z_lt_ge_dec).
Axiom eval_gt_bool : Hnf (eval_int_rel_op Bgt ZArith_dec.Z_gt_le_dec).
Axiom eval_le_bool : Hnf (eval_int_rel_op Ble ZArith_dec.Z_le_gt_dec).
Axiom eval_ge_bool : Hnf (eval_int_rel_op Bge ZArith_dec.Z_ge_lt_dec).

Axiom eval_eq_int : Hnf (eval_int_rel_op_int Beq Z.eq_dec).
Axiom eval_neq_int :
  forall resolve ty a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if Z.eq_dec av bv then 0 else 1)%Z ->
    eval_binop_pure (resolve:=resolve) Bneq ty ty T_int a b (Vint c).
Axiom eval_lt_int : Hnf (eval_int_rel_op_int Blt ZArith_dec.Z_lt_ge_dec).
Axiom eval_gt_int : Hnf (eval_int_rel_op_int Bgt ZArith_dec.Z_gt_le_dec).
Axiom eval_le_int : Hnf (eval_int_rel_op_int Ble ZArith_dec.Z_le_gt_dec).
Axiom eval_ge_int : Hnf (eval_int_rel_op_int Bge ZArith_dec.Z_ge_lt_dec).

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
