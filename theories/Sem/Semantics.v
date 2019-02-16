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

Lemma eval_add : forall ty (a b c : Z),
    c = (Z.add a b) ->
    has_type (Vint c) ty ->
    eval_binop Badd ty (Vint a) (Vint b) (Vint c).
Proof using. Admitted.

Parameter offset_ptr : val -> Z -> val.

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
