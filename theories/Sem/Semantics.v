(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * The "operational" style definitions about C++.
 *
 * The definitions in this file are based (loosely) on CompCert.
 *)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.Ascii.

From Cpp Require Import
     Ast.

(** values *)
Parameter val : Type.

Parameter ptr : Type.
Parameter ptr_eq_dec : forall (x y : ptr), { x = y } + { x <> y }.

Parameter nullptr : ptr.
Parameter Vptr : ptr -> val.
Parameter Vint : Z -> val.

Definition Vchar (a : Ascii.ascii) : val :=
  Vint (Z.of_N (N_of_ascii a)).
Definition Vbool (b : bool) : val :=
  Vint (if b then 1 else 0).


Parameter is_true : val -> bool.
Axiom is_true_int : forall i,
    is_true (Vint i) = negb (BinIntDef.Z.eqb i 0).


Axiom Vint_inj : forall a b, Vint a = Vint b -> a = b.

(* this is the stack frame *)
Parameter region : Type.
(* this is the thread information *)
Parameter thread_info : Type.

Parameter has_type : val -> type -> Prop.

Axiom has_type_pointer : forall v ty, has_type v (Tpointer ty) ->
                                 exists p, v = Vptr p.

Definition bound (bits : nat) (sgn : bool) (v : Z) : Prop :=
  if sgn then
    (-Z.pow 2 (Z.of_nat bits - 1) < v < Z.pow 2 (Z.of_nat bits - 1) - 1)%Z
  else
    (0 <= v < Z.pow 2 (Z.of_nat bits))%Z.

Axiom has_int_type : forall (sz : nat) (sgn : bool) z,
    bound sz sgn z <-> has_type (Vint z) (Tint (Some sz) sgn).

Axiom has_type_qual : forall t q x,
    has_type x (drop_qualifiers t) ->
    has_type x (Tqualified q t).

Hint Resolve has_type_qual : has_type.

Parameter eval_unop : UnOp -> type -> type -> val -> val -> Prop.
Parameter eval_binop : BinOp -> type -> type -> type -> val -> val -> val -> Prop.

Definition eval_int_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall w s (a b c : Z),
    c = o a b ->
    has_type (Vint c) (Tint w s) ->
    eval_binop bo (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* todo(jmgrosen): allow wrapping in the unsigned case *)
Axiom eval_add :
  ltac:(let x := eval hnf in (eval_int_op Badd Z.add) in refine x).
Axiom eval_sub :
  ltac:(let x := eval hnf in (eval_int_op Bsub Z.sub) in refine x).
Axiom eval_mul :
  ltac:(let x := eval hnf in (eval_int_op Bmul Z.mul) in refine x).
Axiom eval_div :
  forall (w : option nat) (s : bool) (a b c : Z),
    b <> 0%Z ->
    c = (a / b)%Z ->
    has_type (Vint c) (Tint w s) ->
    eval_binop Bdiv (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).
Axiom eval_mod :
  forall (w : option nat) (s : bool) (a b c : Z),
    b <> 0%Z ->
    c = (a mod b)%Z ->
    has_type (Vint c) (Tint w s) ->
    eval_binop Bmod (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).
Axiom eval_shl :
  forall w s (a b c : Z),
    (0 <= b < Z.of_nat w)%Z ->
    c = Z.shiftl a b ->
    has_type (Vint c) (Tint (Some w) s) ->
    (* todo(jmgrosen): what to do for [Tint None s]? *)
    eval_binop Bshl (Tint (Some w) s) (Tint (Some w) s) (Tint (Some w) s) (Vint a) (Vint b) (Vint c).
Axiom eval_shr :
  forall w s (a b c : Z),
    (0 <= b < Z.of_nat w)%Z ->
    c = Z.shiftr a b ->
    has_type (Vint c) (Tint (Some w) s) ->
    (* todo(jmgrosen): what to do for [Tint None s]? *)
    eval_binop Bshr (Tint (Some w) s) (Tint (Some w) s) (Tint (Some w) s) (Vint a) (Vint b) (Vint c).

Definition eval_int_rel_op (bo : BinOp) {P Q : Z -> Z -> Prop}
           (o : forall a b : Z, {P a b} + {Q a b}) : Prop :=
  forall w s a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop bo (Tint w s) (Tint w s) Tbool a b (Vint c).

Definition eval_int_rel_op_int (bo : BinOp) {P Q : Z -> Z -> Prop}
           (o : forall a b : Z, {P a b} + {Q a b}) : Prop :=
  forall w s a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop bo (Tint w s) (Tint w s) (T_int) a b (Vint c).

Axiom eval_eq_bool :
  ltac:(let x := eval hnf in (eval_int_rel_op Beq Z.eq_dec) in refine x).
Axiom eval_neq_bool :
  forall ty a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if Z.eq_dec av bv then 0 else 1)%Z ->
    eval_binop Bneq ty ty Tbool a b (Vint c).
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
  forall ty a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if Z.eq_dec av bv then 0 else 1)%Z ->
    eval_binop Bneq ty ty T_int a b (Vint c).
Axiom eval_lt_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Blt ZArith_dec.Z_lt_ge_dec) in refine x).
Axiom eval_gt_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Bgt ZArith_dec.Z_gt_le_dec) in refine x).
Axiom eval_le_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Ble ZArith_dec.Z_le_gt_dec) in refine x).
Axiom eval_ge_int :
  ltac:(let x := eval hnf in (eval_int_rel_op_int Bge ZArith_dec.Z_ge_lt_dec) in refine x).

Axiom eval_ptr_eq :
  forall ty a b av bv c,
    a = Vptr av ->
    b = Vptr bv ->
    c = (if ptr_eq_dec av bv then 1 else 0)%Z ->
    eval_binop Beq (Tpointer ty) (Tpointer ty) Tbool a b (Vint c).
Axiom eval_ptr_neq :
  forall ty a b av bv c,
    a = Vptr av ->
    b = Vptr bv ->
    c = (if ptr_eq_dec av bv then 0 else 1)%Z ->
    eval_binop Bneq (Tpointer ty) (Tpointer ty) Tbool a b (Vint c).

Axiom eval_not_bool : forall a, eval_unop Unot Tbool Tbool (Vbool a) (Vbool (negb a)).


(** global environments
 *)
Parameter genv : Type.

Parameter align_of : forall {c : genv} (t : type) (e : N), Prop.

Parameter glob_addr : genv -> obj_name -> ptr -> Prop.

(* todo(gmm): this isn't sound due to reference fields *)
Parameter offset_of : forall {c : genv} (t : type) (f : ident) (e : Z), Prop.
Parameter parent_offset : forall {c : genv} (t : globname) (f : globname) (e : Z), Prop.

Parameter size_of : forall {c : genv} (t : type) (e : N), Prop.
Axiom size_of_int : forall {c : genv} s w,
    @size_of c (Tint (Some w) s) (N.div (N.of_nat w) 8).
Axiom size_of_char : forall {c : genv} s w,
    @size_of c (Tchar (Some w) s) (N.div (N.of_nat w) 8).
Axiom size_of_bool : forall {c : genv},
    @size_of c Tbool 1.
Parameter pointer_size : N. (* in bytes *)
Axiom size_of_pointer : forall {c : genv} t,
    @size_of c (Tpointer t) pointer_size.

(** pointer offsets
 *)
Parameter offset_ptr : val -> Z -> val. (* todo(gmm): not sound *)
Axiom offset_ptr_combine : forall b o o',
    offset_ptr (offset_ptr b o) o' = offset_ptr b (o + o').
Axiom offset_ptr_0 : forall b,
    offset_ptr b 0 = b.
