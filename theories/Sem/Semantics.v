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

Axiom Vptr_inj : forall p1 p2, Vptr p1 = Vptr p2 -> p1 = p2.
Axiom Vint_inj : forall a b, Vint a = Vint b -> a = b.

(* this is the stack frame *)
Parameter region : Type.
(* this is the thread information *)
Parameter thread_info : Type.


(** pointer offsets
 *)
Parameter offset_ptr : val -> Z -> val.
(* note(gmm): this is not defined according to the C semantics because creating
 * a pointer that goes out of bounds of the object is undefined behavior in C,
 * e.g. [(p + a) - a <> p] if [p + a] is out of bounds.
 *)
Axiom offset_ptr_combine : forall b o o',
    offset_ptr (offset_ptr b o) o' = offset_ptr b (o + o').
Axiom offset_ptr_0 : forall b,
    offset_ptr b 0 = b.

(* All offsets are valid pointers. todo: This is unsound. *)
Parameter offset_ptr_ : ptr -> Z -> ptr.
Axiom offset_ptr_val : forall v o p, Vptr p = v -> Vptr (offset_ptr_ p o) = offset_ptr v o.

Axiom offset_ptr_combine_ : forall b o o',
    offset_ptr_ (offset_ptr_ b o) o' = offset_ptr_ b (o + o').
Axiom offset_ptr_0_ : forall b,
    offset_ptr_ b 0 = b.

(** global environments
 *)
Parameter genv : Type.

Parameter has_type : val -> type -> Prop.

Axiom has_type_pointer : forall v ty, has_type v (Tpointer ty) -> exists p, v = Vptr p.

Definition bound (bits : size) (sgn : signed) (v : Z) : Prop :=
  if sgn then
    (-Z.pow 2 (Z.of_N bits - 1) <= v < Z.pow 2 (Z.of_N bits - 1))%Z
  else
    (0 <= v < Z.pow 2 (Z.of_N bits))%Z.

Axiom has_int_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tint sz sgn).

Axiom has_char_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tchar sz sgn).

Axiom has_type_qual : forall t q x,
    has_type x (drop_qualifiers t) ->
    has_type x (Tqualified q t).

Hint Resolve has_type_qual : has_type.




(* address of a global variable *)
Parameter glob_addr : genv -> obj_name -> ptr -> Prop.

(* todo(gmm): this isn't sound due to reference fields *)
Parameter offset_of : forall (resolve : genv) (t : type) (f : ident) (e : Z), Prop.
Parameter parent_offset : forall (resolve : genv) (t : globname) (f : globname) (e : Z), Prop.

Parameter pointer_size : N. (* in bytes *)


(* sizeof() *)
Parameter size_of : forall (resolve : genv) (t : type) (e : N), Prop.
Axiom size_of_unique : forall {c : genv} t sz sz',
    @size_of c t sz ->
    @size_of c t sz' ->
    sz = sz'.

Axiom size_of_int : forall {c : genv} s w,
    @size_of c (Tint w s) (N.div (w + 7) 8).
Axiom size_of_char : forall {c : genv} s w,
    @size_of c (Tchar w s) (N.div (w + 7) 8).
Axiom size_of_bool : forall {c : genv},
    @size_of c Tbool 1.
Axiom size_of_pointer : forall {c : genv} t,
    @size_of c (Tpointer t) pointer_size.
Axiom size_of_qualified : forall {c : genv} t sz q,
    @size_of c t sz ->
    @size_of c (Tqualified q t) sz.
Axiom size_of_array : forall {c : genv} t n sz,
    @size_of c t sz ->
    @size_of c (Tarray t n) (sz * n).

Lemma size_of_Qmut : forall {c} t sz,
    @size_of c t sz ->
    @size_of c (Qmut t) sz.
Proof.
  intros.
  now apply size_of_qualified.
Qed.

Lemma size_of_Qconst : forall {c} t sz,
    @size_of c t sz ->
    @size_of c (Qconst t) sz.
Proof.
  intros.
  now apply size_of_qualified.
Qed.

(* alignof() *)
Parameter align_of : forall {resolve : genv} (t : type) (e : N), Prop.

(* truncation (used for unsigned operations) *)
Definition trim (w : N) (v : Z) : Z := v mod (2 ^ Z.of_N w).

(* operator semantics *)
Parameter eval_unop : forall {resolve : genv}, UnOp -> forall (argT resT : type) (arg res : val), Prop.
Parameter eval_binop : forall {resolve : genv}, BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), Prop.

Definition eval_ptr_int_op (bo : BinOp) (f : Z -> Z) : Prop :=
  forall resolve t w s p o p' sz,
    size_of resolve t sz ->
    p' = offset_ptr_ p (f o * Z.of_N sz) ->
    eval_binop (resolve:=resolve) bo
               (Tpointer t) (Tint w s) (Tpointer t)
               (Vptr p)     (Vint o)   (Vptr p').

Axiom eval_ptr_int_add :
  ltac:(let x := eval hnf in (eval_ptr_int_op Badd (fun x => x)) in refine x).
Axiom eval_ptr_int_sub :
  ltac:(let x := eval hnf in (eval_ptr_int_op Bsub (fun x => -x)%Z) in refine x).

Definition eval_int_ptr_op (bo : BinOp) (f : Z -> Z) : Prop :=
  forall resolve t w s p o p' sz,
    size_of resolve t sz ->
    p' = offset_ptr_ p (f o * Z.of_N sz) ->
    eval_binop (resolve:=resolve) bo
               (Tint w s) (Tpointer t) (Tpointer t)
               (Vint o)   (Vptr p)     (Vptr p').

Axiom eval_int_ptr_add :
  ltac:(let x := eval hnf in (eval_int_ptr_op Badd (fun x => x)) in refine x).

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
    c = (if s then o a b else trim w (o a b)) ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

Definition eval_int_bin_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall resolve w (s : signed) (a b c : Z),
    c = (if s then o a b else trim w (o a b)) ->
    eval_binop (resolve:=resolve) bo (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

(* todo(jmgrosen): allow wrapping in the unsigned case *)
Axiom eval_add :
  ltac:(let x := eval hnf in (eval_int_op Badd Z.add) in refine x).
Axiom eval_sub :
  ltac:(let x := eval hnf in (eval_int_op Bsub Z.sub) in refine x).
Axiom eval_mul :
  ltac:(let x := eval hnf in (eval_int_op Bmul Z.mul) in refine x).
Axiom eval_or :
  ltac:(let x := eval hnf in (eval_int_op Bor Z.lor) in refine x).
Axiom eval_and :
  ltac:(let x := eval hnf in (eval_int_op Band Z.land) in refine x).
Axiom eval_xor :
  ltac:(let x := eval hnf in (eval_int_op Bxor Z.lxor) in refine x).
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

(* note(gmm): the semantics of shifting has changed a lot over the different
 * c++ standards.
 *)
Axiom eval_shl :
  forall resolve (w : N) (s : signed) (a b c : Z),
    (0 <= b < Z.of_N w)%Z ->
    (c = if s then Z.shiftl a b else trim w (Z.shiftl a b)) ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) Bshl (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).
Axiom eval_shr :
  forall resolve (w : N) (s : signed) (a b c : Z),
    (0 <= b < Z.of_N w)%Z ->
    (c = if s then Z.shiftr a b else trim w (Z.shiftr a b)) ->
    has_type (Vint c) (Tint w s) ->
    eval_binop (resolve:=resolve) Bshr (Tint w s) (Tint w s) (Tint w s) (Vint a) (Vint b) (Vint c).

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

Axiom eval_not_bool : forall resolve a,
    eval_unop (resolve:=resolve) Unot Tbool Tbool (Vbool a) (Vbool (negb a)).

Axiom eval_minus_int : forall resolve s a c w bytes,
    size_of resolve (Tint w s) bytes ->
    c = (if s then (0 - a) else trim w (0 - a))%Z ->
    has_type (Vint c) (Tint w s) ->
    eval_unop (resolve:=resolve) Uminus (Tint w s) (Tint w s)
              (Vint a) (Vint c).
