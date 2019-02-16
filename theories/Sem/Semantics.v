(**
 * The "operational" style definitions about C++.
 *
 * The definitions in this file are based (loosely) on CompCert.
 *)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
From Cpp Require Import
     Ast.

(** values *)
Parameter val : Type.

Parameter ptr : Type.

Parameter Vptr : ptr -> val.
Parameter Vint : Z -> val.

(* this is the stack frame *)
Parameter region : Type.
(* this is the thread information *)
Parameter thread_info : Type.

Parameter has_type : val -> type -> Prop.

Axiom has_type_int : forall z,
    (-Z.pow 2 31 < z < Z.pow 2 31 - 1)%Z ->
    has_type (Vint z) T_int.
Axiom has_type_int32 : forall z,
    (-Z.pow 2 31 < z < Z.pow 2 31 - 1)%Z ->
    has_type (Vint z) T_int32.

(* this is an axiom *)
Axiom has_type_int_any : forall x, has_type (Vint x) T_int.
Axiom has_type_int_bound : forall {x},
    has_type (Vint x) T_int ->
    (-(2^31) < x < 2^31 - 1)%Z.
Axiom has_type_qual : forall t q x,
    has_type x (drop_qualifiers t) ->
    has_type x (Tqualified q t).

Hint Resolve has_type_int_any has_type_int_bound has_type_qual
  : has_type.


Parameter eval_unop : UnOp -> type -> val -> val -> Prop.
Parameter eval_binop : BinOp -> type -> val -> val -> val -> Prop.

Definition eval_int_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall w s (a b c : Z),
    c = o a b ->
    has_type (Vint c) (Tint w s) ->
    eval_binop bo (Tint w s) (Vint a) (Vint b) (Vint c).

Axiom eval_add :
  ltac:(let x := eval hnf in (eval_int_op Badd Z.add) in refine x).
Axiom eval_sub :
  ltac:(let x := eval hnf in (eval_int_op Bsub Z.sub) in refine x).
Axiom eval_ :
  ltac:(let x := eval hnf in (eval_int_op Bmul Z.mul) in refine x).
Axiom eval_div :
  ltac:(let x := eval hnf in (eval_int_op Bdiv Z.div) in refine x).
Axiom eval_mod :
  ltac:(let x := eval hnf in (eval_int_op Bmod Z.modulo) in refine x).

Definition eval_int_rel_op (bo : BinOp) {P Q : Z -> Z -> Prop}
           (o : forall a b : Z, {P a b} + {Q a b}) : Prop :=
  forall w s a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if o av bv then 1 else 0)%Z ->
    eval_binop bo (Tint w s) a b (Vint c).

Axiom eval_eq :
  ltac:(let x := eval hnf in (eval_int_rel_op Beq Z.eq_dec) in refine x).
Axiom eval_neq :
  forall ty a b (av bv : Z) (c : Z),
    a = Vint av ->
    b = Vint bv ->
    c = (if Z.eq_dec av bv then 0 else 1)%Z ->
    eval_binop Bneq ty a b (Vint c).
Axiom eval_lt :
  ltac:(let x := eval hnf in (eval_int_rel_op Blt ZArith_dec.Z_lt_ge_dec) in refine x).
Axiom eval_gt :
  ltac:(let x := eval hnf in (eval_int_rel_op Bgt ZArith_dec.Z_gt_le_dec) in refine x).
Axiom eval_le :
  ltac:(let x := eval hnf in (eval_int_rel_op Ble ZArith_dec.Z_le_gt_dec) in refine x).
Axiom eval_ge :
  ltac:(let x := eval hnf in (eval_int_rel_op Bge ZArith_dec.Z_ge_lt_dec) in refine x).

Parameter offset_ptr : val -> Z -> val.
Axiom offset_ptr_combine : forall b o o',
    offset_ptr (offset_ptr b o) o' = offset_ptr b (o + o').
Axiom offset_ptr_0 : forall b,
    offset_ptr b 0 = b.

Parameter is_true : val -> bool.
Axiom is_true_int : forall i,
    is_true (Vint i) =
    BinIntDef.Z.eqb i 0.

(** global environments
 *)
Parameter genv : Type.



Parameter glob_addr : genv -> obj_name -> ptr -> Prop.

Parameter offset_of : forall {c : genv} (t : type) (f : ident) (e : Z), Prop.

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
