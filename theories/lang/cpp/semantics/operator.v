(*
 * Copyright (c) 2020-22 BedRock Systems, Inc.
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

#[local] Open Scope Z_scope.

Module Type OPERATOR_INTF_FUNCTOR
  (Import P : PTRS_INTF)
  (Import INTF : VALUES_INTF_FUNCTOR PTRS_INTF_AXIOM).
  (** operator semantics *)
  Parameter eval_unop : translation_unit -> UnOp -> forall (argT resT : type) (arg res : val), Prop.
  Parameter eval_binop_pure : translation_unit -> BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), Prop.

Section operator_axioms.
  Context {σ : genv} (tu : translation_unit).
  #[local] Notation eval_unop := (eval_unop tu).
  #[local] Notation eval_binop_pure := (eval_binop_pure tu).

(** * Unary Operators *)

(* The builtin unary `!` operator logically negates its argument, i.e. `true` -> `false` and
   `false` -> `true`.
   https://eel.is/c++draft/expr.unary.op#9
 *)
Axiom eval_not_bool : forall a,
    eval_unop Unot Tbool Tbool (Vbool a) (Vbool (negb a)).

(* The builtin unary `~` operator computes the bitwise negation of the operator
   https://eel.is/c++draft/expr.unary.op#10

   NOTE [Z.lnot a = -1 - a]
 *)
Axiom eval_unop_not : forall (w : bitsize) (sgn : signed) (a b : Z),
    b = match sgn with Signed => -1 - a | Unsigned => bitFlipZU w a end ->
    has_type (Vint b) (Tnum w sgn) ->
    eval_unop Ubnot (Tnum w sgn) (Tnum w sgn)
              (Vint a) (Vint b).

(* The builtin unary `+` operator is the identity on arithmetic types.
   https://eel.is/c++draft/expr.unary.op#7
 *)
Axiom eval_plus_int : forall (s : signed) a w,
    has_type (Vint a) (Tnum w s) ->
    eval_unop Uplus (Tnum w s) (Tnum w s)
              (Vint a) (Vint a).

(* The builtin unary `-` operator calculates the negative of its
   promoted operand. For unsigned a, the value of -a is 2^b -a, where b
   is the number of bits after promotion.
   https://eel.is/c++draft/expr.unary.op#8
 *)
Axiom eval_minus_int : forall (s : signed) a c w,
    c = match s with
        | Signed => 0 - a
        | Unsigned => trim (bitsN w) (0 - a)
        end ->
    has_type (Vint c) (Tnum w s) ->
    eval_unop Uminus (Tnum w s) (Tnum w s)
              (Vint a) (Vint c).

(** * Binary Operators *)

(** ** arithmetic operators *)
Let eval_int_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall w (s : signed) (a b c : Z),
    has_type (Vint a) (Tnum w s) ->
    has_type (Vint b) (Tnum w s) ->
    c = match s with
        | Signed => o a b
        | Unsigned => trim (bitsN w) (o a b)
        end ->
    has_type (Vint c) (Tnum w s) ->
    eval_binop_pure bo (Tnum w s) (Tnum w s) (Tnum w s) (Vint a) (Vint b) (Vint c).

Axiom eval_add : Hnf (eval_int_op Badd Z.add).
Axiom eval_sub : Hnf (eval_int_op Bsub Z.sub).
Axiom eval_mul : Hnf (eval_int_op Bmul Z.mul).

(* The binary operator / divides the first operand by the second, after usual
   arithmetic conversions.
   The quotient is truncated towards zero (fractional part is discarded),
   since C++11.
   If the second operand is zero, the behavior is undefined. *)
Axiom eval_div :
  forall (w : bitsize) (s : signed) (a b c : Z),
    b <> 0%Z ->
    has_type (Vint a) (Tnum w s) ->
    has_type (Vint b) (Tnum w s) ->
    c = Z.quot a b ->
    eval_binop_pure Bdiv (Tnum w s) (Tnum w s) (Tnum w s) (Vint a) (Vint b) (Vint c).
Axiom eval_mod :
  forall (w : bitsize) (s : signed) (a b c : Z),
    b <> 0%Z ->
    has_type (Vint a) (Tnum w s) ->
    has_type (Vint b) (Tnum w s) ->
    c = Z.rem a b ->
    eval_binop_pure Bmod (Tnum w s) (Tnum w s) (Tnum w s) (Vint a) (Vint b) (Vint c).

(** ** bitwise operators *)
Let eval_int_bitwise_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall w (s : signed) (a b c : Z),
    has_type (Vint a) (Tnum w s) ->
    has_type (Vint b) (Tnum w s) ->
    c = o a b -> (* note that bitwise operators respect bounds *)
    eval_binop_pure bo (Tnum w s) (Tnum w s) (Tnum w s) (Vint a) (Vint b) (Vint c).

(* bitwise(logical) operators *)
Axiom eval_or : Hnf (eval_int_bitwise_op Bor Z.lor).
Axiom eval_and : Hnf (eval_int_bitwise_op Band Z.land).
Axiom eval_xor : Hnf (eval_int_bitwise_op Bxor Z.lxor).

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
  forall (w : bitsize) w2 (s s2 : signed) (a b c : Z),
    (0 <= b < bitsZ w)%Z ->
    (0 <= a)%Z ->
    has_type (Vint a) (Tnum w s) ->
    has_type (Vint b) (Tnum w2 s2) ->
    c = match s with
        | Signed => Z.shiftl a b
        | Unsigned => trim (bitsN w) (Z.shiftl a b)
        end ->
    has_type (Vint c) (Tnum w s) ->
    eval_binop_pure Bshl (Tnum w s) (Tnum w2 s2) (Tnum w s) (Vint a) (Vint b) (Vint c).

(* C++14 <= VER < C++20: The value of E1 >> E2 is E1 right-shifted E2 bit
   positions. If E1 has an unsigned type or if E1 has a signed type
   and a non-negative value, the value of the result is the integral
   part of the quotient of E1/(2^E2). If E1 has a signed type and a
   negative value, the resulting value is implementation-defined. *)
Axiom eval_shr :
  forall (w : bitsize) w2 (s s2: signed) (a b c : Z),
    (0 <= b < bitsZ w)%Z ->
    (0 <= a)%Z ->
    has_type (Vint a) (Tnum w s) ->
    has_type (Vint b) (Tnum w2 s2) ->
    c = match s with Signed => Z.shiftr a b | Unsigned => trim (bitsN w) (Z.shiftr a b) end ->
    eval_binop_pure Bshr (Tnum w s) (Tnum w2 s2) (Tnum w s) (Vint a) (Vint b) (Vint c).

(** ** comparison operators *)

(** [relop_result_type ty] holds on types [ty] that can be the result of a relational
    operator comparison, e.g. `==` or `<`.
    In C++ this is the type `bool`, in C this is the type `int`.
 *)
Definition relop_result_type (ty : type) : Prop :=
  match ty with
  | Tint (* this is literally the type `int`, *not* any numeric type *)
  | Tbool => True
  | _ => False
  end.

(** [relop_int_comparable ty] holds on types [ty] that have integral comparison
    semantics when comparing them.
    These are bool, integral types, and enum types.
 *)
Definition relop_int_comparable (ty : type) : Prop :=
  match ty with
  | Tenum _
  | Tnum _ _
  | Tbool => True
  | _ => False
  end.

(* injection of [bool] into [Z]
 *)
Definition b2i (b : bool) : Z := if b then 1 else 0.

(* Integer conversions are used to compare unscoped enumeration types but not
   scoped ones. Therefore, we include comparisons on enum. The values are
   compared after integer conversion.

   Note that the [has_type] facts guarantees that the enum is valid if [ty] is
   an enum. *)
#[local] Definition eval_int_rel_op (o : Z -> Z -> Prop) {RD : RelDecision o} (bo : BinOp) : Prop :=
  forall ty ty' (av bv : Z),
    let a := Vint av in
    let b := Vint bv in
    relop_int_comparable ty ->
    relop_result_type ty' ->
    has_type a ty ->
    has_type b ty ->
    eval_binop_pure bo ty ty ty' a b (Vbool $ bool_decide (o av bv)).

Axiom eval_eq : Hnf (eval_int_rel_op eq Beq).
Axiom eval_neq : Hnf (eval_int_rel_op (fun a b => a <> b) (RD:=ltac:(red; refine _)) Bneq).
Axiom eval_lt : Hnf (eval_int_rel_op Z.lt Blt).
Axiom eval_gt : Hnf (eval_int_rel_op Z.gt Bgt).
Axiom eval_le : Hnf (eval_int_rel_op Z.le Ble).
Axiom eval_ge : Hnf (eval_int_rel_op Z.ge Bge).

End operator_axioms.
End OPERATOR_INTF_FUNCTOR.

(* Collect all the axioms. *)

Module Export OPERATOR_INTF_AXIOM <: OPERATOR_INTF_FUNCTOR PTRS_INTF_AXIOM VALUES_INTF_AXIOM.
  Include OPERATOR_INTF_FUNCTOR PTRS_INTF_AXIOM VALUES_INTF_AXIOM.
End OPERATOR_INTF_AXIOM.

(** for pre- and post- increment/decrement, this function determines the type
    of the [1] that is added or subtracted.
 *)
Fixpoint companion_type (t : type) : option type :=
  match t with
  | Tpointer _ => Some (Tnum int_bits Signed)
  | Tnum _ _ => Some t
  | Tqualified _ t => companion_type t
  | _ => None
  end.

(* [1] is well-typed in any type that is a companion type *)
Lemma companion_type_1 {σ : genv} t : forall ct,
    companion_type t = Some ct ->
    has_type 1 ct.
Proof.
  induction t; simpl; try congruence; eauto.
  - inversion 1; subst. by apply has_int_type.
  - inversion 1; subst. apply has_int_type. destruct size, signed; done.
Qed.
