(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
From bedrock.lang.cpp.syntax Require Import names types.

Set Primitive Projections.

Variant UnOp : Set :=
| Uminus
| Unot
| Ubnot
| Uother (_ : bs).
Instance: EqDecision UnOp.
Proof. solve_decision. Defined.

Variant BinOp : Set :=
| Badd
| Band (* & *)
| Bcmp (* <=> *)
| Bdiv (* / *)
| Beq
| Bge
| Bgt
| Ble
| Blt
| Bmul
| Bneq
| Bor  (* | *)
| Bmod
| Bshl
| Bshr
| Bsub
| Bxor (* ^ *)
| Bdotp (* .* *)
| Bdotip (* ->* *)
.
Instance: EqDecision BinOp.
Proof. solve_decision. Defined.


Variant AtomicOp : Set :=
| AO__atomic_load
| AO__atomic_load_n
| AO__atomic_store
| AO__atomic_store_n
| AO__atomic_compare_exchange
| AO__atomic_compare_exchange_n
| AO__atomic_exchange
| AO__atomic_exchange_n
| AO__atomic_fetch_add
| AO__atomic_fetch_sub
| AO__atomic_fetch_and
| AO__atomic_fetch_or
| AO__atomic_fetch_xor
| AO__atomic_fetch_nand
| AO__atomic_add_fetch
| AO__atomic_sub_fetch
| AO__atomic_and_fetch
| AO__atomic_or_fetch
| AO__atomic_xor_fetch
| AO__atomic_nand_fetch
.
Instance: EqDecision AtomicOp.
Proof. solve_decision. Defined.

Variant BuiltinFn : Set :=
| Bin_alloca
| Bin_alloca_with_align
| Bin_launder
| Bin_expect
| Bin_unreachable
| Bin_trap
| Bin_bswap16
| Bin_bswap32
| Bin_bswap64
| Bin_bswap128
| Bin_bzero
| Bin_ffs
| Bin_ffsl
| Bin_ffsll
| Bin_clz
| Bin_clzl
| Bin_clzll
| Bin_ctz
| Bin_ctzl
| Bin_ctzll
| Bin_popcount
| Bin_popcountl
| Bin_unknown (_ : bs)
.
Instance: EqDecision BuiltinFn.
Proof. solve_decision. Defined.

(** * Casts *)
Variant Cast : Set :=
| Cdependent (* this doesn't have any semantics *)
| Cbitcast
| Clvaluebitcast
| Cl2r
| Cnoop
| Carray2pointer
| Cfunction2pointer
| Cint2pointer
| Cpointer2int
| Cptr2bool
| Cderived2base
| Cbase2derived
| Cintegral
| Cint2bool
| Cnull2ptr
| Cbuiltin2function
| Cconstructorconversion
| C2void
| Cuser        (conversion_function : obj_name)
| Creinterpret (_ : type)
| Cstatic      (from to : globname)
| Cdynamic     (from to : globname)
| Cconst       (_ : type).
Instance Cast_eqdec: EqDecision Cast.
Proof. solve_decision. Defined.

(** * References *)
Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).
Instance: EqDecision VarRef.
Proof. solve_decision. Defined.

Variant call_type : Set := Virtual | Direct.
Instance: EqDecision call_type.
Proof. solve_decision. Defined.

Variant ValCat : Set := Lvalue | Prvalue | Xvalue.
Instance: EqDecision ValCat.
Proof. solve_decision. Defined.

Inductive Expr : Set :=
| Econst_ref (_ : VarRef) (_ : type)
  (* ^ these are different because they do not have addresses *)
| Evar     (_ : VarRef) (_ : type)
  (* ^ local and global variable reference *)

| Echar    (_ : Z) (_ : type)
| Estring  (_ : bs) (_ : type)
| Eint     (_ : Z) (_ : type)
| Ebool    (_ : bool)
  (* ^ literals *)

| Eunop    (_ : UnOp) (_ : Expr) (_ : type)
| Ebinop   (_ : BinOp) (_ _ : Expr) (_ : type)
 (* ^ note(gmm): overloaded operators are already resolved. so an overloaded
  * operator shows up as a function call, not a `Eunop` or `Ebinop`.
  * this includes the assignment operator for classes.
  *)
| Ederef (_ : Expr) (_ : type) (* XXX type = strip pointer from (type_of e) *)
| Eaddrof (_ : Expr)
| Eassign (_ _ : Expr) (_ : type) (* = type of lhs, if not dependent *)
| Eassign_op (_ : BinOp) (_ _ : Expr) (_ : type)
  (* ^ these are specialized because they are common *)

| Epreinc (_ : Expr) (_ : type)
| Epostinc (_ : Expr) (_ : type)
| Epredec (_ : Expr) (_ : type)
| Epostdec (_ : Expr) (_ : type)
  (* ^ special unary operators *)

| Eseqand (_ _ : Expr)
| Eseqor  (_ _ : Expr)
| Ecomma (vc : ValCat) (e1 e2 : Expr)
  (* ^ these are specialized because they have special control flow semantics *)

| Ecall    (_ : Expr) (_ : list (ValCat * Expr)) (_ : type)
| Ecast    (_ : Cast) (_ : ValCat * Expr) (_ : type)

| Emember  (_ : ValCat) (obj : Expr) (_ : field) (_ : type)
  (* TODO: maybe replace the left branch use [Expr] here? *)
| Emember_call (method : (obj_name * call_type * type) + Expr) (_ : ValCat) (obj : Expr) (_ : list (ValCat * Expr)) (_ : type)

| Esubscript (_ : Expr) (_ : Expr) (_ : type)
| Esize_of (_ : type + Expr) (_ : type)
| Ealign_of (_ : type + Expr) (_ : type)
| Econstructor (_ : obj_name) (_ : list (ValCat * Expr)) (_ : type)
| Eimplicit (_ : Expr)
| Eimplicit_init (_ : type)
| Eif       (_ _ _ : Expr) (_ : type)

| Ethis (_ : type)
| Enull
| Einitlist (_ : list Expr) (_ : option Expr) (_ : type)

| Enew (new_fn : option (obj_name * type)) (new_args : list (ValCat * Expr))
       (alloc_ty : type)
       (array_size : option Expr) (init : option Expr) (_ : type)
| Edelete (is_array : bool) (delete_fn : option (obj_name * type)) (arg : Expr)
          (deleted_type : type) (_ : type)

| Eandclean (_ : Expr)
| Ematerialize_temp (_ : Expr)

| Ebuiltin (_ : BuiltinFn) (_ : type)
| Eatomic (_ : AtomicOp) (_ : list (ValCat * Expr)) (_ : type)
| Eva_arg (_ : Expr) (_ : type)
| Epseudo_destructor (_ : type) (_ : Expr)

| Earrayloop_init (oname : N) (src : ValCat * Expr) (level : N) (length : N) (init : Expr) (_ : type)
| Earrayloop_index (level : N) (_ : type)
| Eopaque_ref (name : N) (_ : type)

| Eunsupported (_ : bs) (_ : type).
Instance Expr_eq_dec : EqDecision Expr.
Proof.
  rewrite /RelDecision /Decision.
  fix IHe 1.
  rewrite -{1}/(EqDecision Expr) in IHe.
  decide equality; try solve_trivial_decision.
Defined.

Definition Edefault_init_expr (e : Expr) : Expr := e.
