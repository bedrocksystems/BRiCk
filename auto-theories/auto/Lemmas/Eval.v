(*
 * Copyright (C) BedRock Systems Inc. 2019 John Grosen
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.

From Cpp Require Import
     Ast Sem.
From Cpp.Auto Require Import
     Discharge.

Local Ltac work :=
  discharge fail idtac fail fail eauto.


Definition wp_eval_unop (uo : UnOp) (t t' : type) (a : val) (P : val -> mpred) : mpred :=
  Exists b : val, embed (eval_unop uo t t' a b) //\\ P b.

Lemma wp_eval_unop_defn : forall uo t t' a P,
    wp_eval_unop uo t t' a P -|- Exists b : val, embed (eval_unop uo t t' a b) //\\ P b.
Proof. reflexivity. Qed.

Definition wp_eval_binop (bo : BinOp) (t1 t2 t' : type) (a b : val) (P : val -> mpred) : mpred :=
  Exists c : val, embed (eval_binop bo t1 t2 t' a b c) //\\ P c.

Lemma wp_eval_binop_defn : forall bo t1 t2 t' a b P,
    wp_eval_binop bo t1 t2 t' a b P -|- Exists c : val, embed (eval_binop bo t1 t2 t' a b c) //\\ P c.
Proof. reflexivity. Qed.



Definition wp_eval_int_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall t1 t2 t3 w s a b av bv Q,
    (* note(jmgrosen): this order of hypotheses is important. we have to unify
       the types first in order to know how to solve the has_type obligation. *)
    (* note(jmgrosen): why do we have this unification of types, rather than
       writing the types in the conclusion? we often have drop_qualifiers,
       Talias, or other similar constructions that need to be reduced in order
       to unify, so we handle that after the fact with reflexivity. *)
    t1 = Tint w s ->
    t2 = Tint w s ->
    t3 = Tint w s ->
    a = Vint av ->
    b = Vint bv ->
    has_type (Vint (o av bv)) (Tint w s) ->
    Q (Vint (o av bv))
    |-- wp_eval_binop bo t1 t2 t3 a b Q.

Local Ltac prove_binop a :=
  intros;
  rewrite wp_eval_binop_defn;
  work;
  eapply embedPropR;
  subst;
  eapply a;
  eauto.

Lemma wp_eval_add : ltac:(let x := eval hnf in (wp_eval_int_op Badd Z.add) in refine x).
Proof. prove_binop eval_add. Qed.

Lemma wp_eval_sub : ltac:(let x := eval hnf in (wp_eval_int_op Bsub Z.sub) in refine x).
Proof. prove_binop eval_sub. Qed.

Lemma wp_eval_mul : ltac:(let x := eval hnf in (wp_eval_int_op Bmul Z.mul) in refine x).
Proof. prove_binop eval_mul. Qed.

Lemma wp_eval_div : forall t1 t2 t3 w s a b av bv Q,
    t1 = Tint w s ->
    t2 = Tint w s ->
    t3 = Tint w s ->
    a = Vint av ->
    b = Vint bv ->
    bv <> 0%Z ->
    has_type (Vint (av / bv)%Z) (Tint w s) ->
    Q (Vint (av / bv)%Z)
    |-- wp_eval_binop Bdiv t1 t2 t3 a b Q.
Proof. prove_binop eval_div. Qed.

Lemma wp_eval_mod : ltac:(let x := eval hnf in (wp_eval_int_op Bmod Z.modulo) in refine x).
Proof. prove_binop eval_mod. Qed.

Lemma wp_eval_shl : ltac:(let x := eval hnf in (wp_eval_int_op Bshl Z.shiftl) in refine x).
Proof. prove_binop eval_shl. Qed.

Lemma wp_eval_shr : ltac:(let x := eval hnf in (wp_eval_int_op Bshr Z.shiftr) in refine x).
Proof. prove_binop eval_shr. Qed.

Definition wp_eval_int_rel_op (bo : BinOp) {P P' : Z -> Z -> Prop}
           (o : forall a b, {P a b} + {P' a b}) : Prop :=
  forall t1 t2 t3 w s a b av bv (Q : val -> mpred),
    t1 = Tint w s ->
    t2 = Tint w s ->
    t3 = Tbool ->
    a = Vint av ->
    b = Vint bv ->
    Q (Vint (if o av bv then 1 else 0)%Z)
    |-- wp_eval_binop bo t1 t2 t3 a b Q.

Lemma wp_eval_eq_bool : ltac:(let x := eval hnf in (wp_eval_int_rel_op Beq Z.eq_dec) in refine x).
Proof. prove_binop eval_eq_bool. Qed.

Lemma wp_eval_neq_bool : forall t1 t2 t3 w s a b av bv (Q : val -> mpred),
    t1 = Tint w s ->
    t2 = Tint w s ->
    t3 = Tbool ->
    a = Vint av ->
    b = Vint bv ->
    Q (Vint (if Z.eq_dec av bv then 0 else 1)%Z)
    |-- wp_eval_binop Bneq t1 t2 t3 av bv Q.
Proof. prove_binop eval_neq_bool. Qed.

Lemma wp_eval_lt_bool : ltac:(let x := eval hnf in (wp_eval_int_rel_op Blt ZArith_dec.Z_lt_ge_dec) in refine x).
Proof. prove_binop eval_lt_bool. Qed.

Lemma wp_eval_gt_bool : ltac:(let x := eval hnf in (wp_eval_int_rel_op Bgt ZArith_dec.Z_gt_le_dec) in refine x).
Proof. prove_binop eval_gt_bool. Qed.

Lemma wp_eval_le_bool : ltac:(let x := eval hnf in (wp_eval_int_rel_op Ble ZArith_dec.Z_le_gt_dec) in refine x).
Proof. prove_binop eval_le_bool. Qed.

Lemma wp_eval_ge_bool : ltac:(let x := eval hnf in (wp_eval_int_rel_op Bge ZArith_dec.Z_ge_lt_dec) in refine x).
Proof. prove_binop eval_ge_bool. Qed.

Definition wp_eval_int_rel_op_int (bo : BinOp) {P P' : Z -> Z -> Prop}
           (o : forall a b, {P a b} + {P' a b}) : Prop :=
  forall t1 t2 t3 w s a b av bv (Q : val -> mpred),
    t1 = Tint w s ->
    t2 = Tint w s ->
    t3 = T_int ->
    a = Vint av ->
    b = Vint bv ->
    Q (Vint (if o av bv then 1 else 0)%Z)
    |-- wp_eval_binop bo t1 t2 t3 a b Q.

Lemma wp_eval_eq_int : ltac:(let x := eval hnf in (wp_eval_int_rel_op_int Beq Z.eq_dec) in refine x).
Proof. prove_binop eval_eq_int. Qed.

Lemma wp_eval_neq_int : forall t1 t2 t3 w s a b av bv (Q : val -> mpred),
    t1 = Tint w s ->
    t2 = Tint w s ->
    t3 = T_int ->
    a = Vint av ->
    b = Vint bv ->
    Q (Vint (if Z.eq_dec av bv then 0 else 1)%Z)
    |-- wp_eval_binop Bneq (Tint w s) (Tint w s) T_int av bv Q.
Proof. prove_binop eval_neq_int. Qed.

Lemma wp_eval_lt_int : ltac:(let x := eval hnf in (wp_eval_int_rel_op_int Blt ZArith_dec.Z_lt_ge_dec) in refine x).
Proof. prove_binop eval_lt_int. Qed.

Lemma wp_eval_gt_int : ltac:(let x := eval hnf in (wp_eval_int_rel_op_int Bgt ZArith_dec.Z_gt_le_dec) in refine x).
Proof. prove_binop eval_gt_int. Qed.

Lemma wp_eval_le_int : ltac:(let x := eval hnf in (wp_eval_int_rel_op_int Ble ZArith_dec.Z_le_gt_dec) in refine x).
Proof. prove_binop eval_le_int. Qed.

Lemma wp_eval_ge_int : ltac:(let x := eval hnf in (wp_eval_int_rel_op_int Bge ZArith_dec.Z_ge_lt_dec) in refine x).
Proof. prove_binop eval_ge_int. Qed.

Lemma wp_eval_ptr_eq : forall t1 t2 t3 ty a b ap bp (Q : val -> mpred),
    t1 = Tpointer ty ->
    t2 = Tpointer ty ->
    t3 = Tbool ->
    a = Vptr ap ->
    b = Vptr bp ->
    Q (Vint (if ptr_eq_dec ap bp then 1 else 0)%Z)
    |-- wp_eval_binop Beq t1 t2 Tbool a b Q.
Proof. prove_binop eval_ptr_eq. Qed.

Lemma wp_eval_ptr_neq : forall t1 t2 t3 ty a b ap bp (Q : val -> mpred),
    t1 = Tpointer ty ->
    t2 = Tpointer ty ->
    t3 = Tbool ->
    a = Vptr ap ->
    b = Vptr bp ->
    Q (Vint (if ptr_eq_dec ap bp then 0 else 1)%Z)
    |-- wp_eval_binop Bneq t1 t2 Tbool a b Q.
Proof. prove_binop eval_ptr_neq. Qed.

Local Ltac prove_unop a :=
  intros;
  rewrite wp_eval_unop_defn;
  work;
  eapply embedPropR;
  subst;
  eapply a;
  eauto.

Lemma wp_eval_not_bool : forall t1 t2 a av (Q : val -> mpred),
    t1 = Tbool ->
    t2 = Tbool ->
    a = Vbool av ->
    Q (Vbool (negb av))
    |-- wp_eval_unop Unot t1 t2 a Q.
Proof. prove_unop eval_not_bool. Qed.

Global Opaque wp_eval_unop wp_eval_binop.
