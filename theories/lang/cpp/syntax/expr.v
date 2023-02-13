(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
From bedrock.lang.cpp.syntax Require Import names types.

Set Primitive Projections.

Variant UnOp : Set :=
| Uminus	(* - *)
| Uplus	(* + *)
| Unot	(* ! *)
| Ubnot	(* ~ *)
| Uunsupported (_ : bs).
#[global] Instance: EqDecision UnOp.
Proof. solve_decision. Defined.
#[global] Instance UnOp_countable : Countable UnOp.
Proof.
  apply (inj_countable' (fun op =>
    match op with
    | Uminus => GenNode 0 []
    | Uplus => GenNode 1 []
    | Unot => GenNode 2 []
    | Ubnot => GenNode 3 []
    | Uunsupported op => GenNode 4 [GenLeaf op]
    end) (fun t =>
    match t with
    | GenNode 0 [] => Uminus
    | GenNode 1 [] => Uplus
    | GenNode 2 [] => Unot
    | GenNode 3 [] => Ubnot
    | GenNode 4 [GenLeaf op] => Uunsupported op
    | _ => Uminus	(* dummy *)
    end)).
  abstract (by intros []).
Defined.

Variant BinOp : Set :=
| Badd	(* + *)
| Band	(* & *)
| Bcmp	(* <=> *)
| Bdiv	(* / *)
| Beq	(* == *)
| Bge	(* >= *)
| Bgt	(* > *)
| Ble	(* <= *)
| Blt	(* < *)
| Bmul	(* * *)
| Bneq	(* != *)
| Bor	(* | *)
| Bmod	(* % *)
| Bshl	(* << *)
| Bshr	(* >> *)
| Bsub	(* - *)
| Bxor	(* ^ *)
| Bdotp	(* .* *)
| Bdotip	(* ->* *)
| Bunsupported (_ : bs).
#[global] Instance: EqDecision BinOp.
Proof. solve_decision. Defined.
#[global] Instance BinOp_countable : Countable BinOp.
Proof.
  apply (inj_countable' (fun op =>
    match op with
    | Badd => GenNode 0 []
    | Band => GenNode 1 []
    | Bcmp => GenNode 2 []
    | Bdiv => GenNode 3 []
    | Beq => GenNode 4 []
    | Bge => GenNode 5 []
    | Bgt => GenNode 6 []
    | Ble => GenNode 7 []
    | Blt => GenNode 8 []
    | Bmul => GenNode 9 []
    | Bneq => GenNode 10 []
    | Bor => GenNode 11 []
    | Bmod => GenNode 12 []
    | Bshl => GenNode 13 []
    | Bshr => GenNode 14 []
    | Bsub => GenNode 15 []
    | Bxor => GenNode 16 []
    | Bdotp => GenNode 17 []
    | Bdotip => GenNode 18 []
    | Bunsupported op => GenNode 19 [GenLeaf op]
    end) (fun t =>
    match t with
    | GenNode 0 [] => Badd
    | GenNode 1 [] => Band
    | GenNode 2 [] => Bcmp
    | GenNode 3 [] => Bdiv
    | GenNode 4 [] => Beq
    | GenNode 5 [] => Bge
    | GenNode 6 [] => Bgt
    | GenNode 7 [] => Ble
    | GenNode 8 [] => Blt
    | GenNode 9 [] => Bmul
    | GenNode 10 [] => Bneq
    | GenNode 11 [] => Bor
    | GenNode 12 [] => Bmod
    | GenNode 13 [] => Bshl
    | GenNode 14 [] => Bshr
    | GenNode 15 [] => Bsub
    | GenNode 16 [] => Bxor
    | GenNode 17 [] => Bdotp
    | GenNode 18 [] => Bdotip
    | GenNode 19 [GenLeaf op] => Bunsupported op
    | _ => Badd	(* dummy *)
    end)).
  abstract (by intros []).
Defined.

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
#[global] Instance: EqDecision AtomicOp.
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
#[global] Instance: EqDecision BuiltinFn.
Proof. solve_decision. Defined.

(** * Casts *)
Inductive Cast' {type : Set} : Set :=
| Cdependent (* this doesn't have any semantics *)
| Cbitcast	(** TODO (FM-3431): This explicit cast expression could carry the type as written *)
| Clvaluebitcast	(** TODO (FM-3431): Drop this constructor? *)
| Cl2r
| Cnoop
| Carray2ptr
| Cfun2ptr
| Cint2ptr
| Cptr2int
| Cptr2bool
  (* in [Cderived2base] and [Cbase2derived], the list is a tree
     from (top..bottom], i.e. **in both cases** the most derived
     class is not included in the list and the base class is at
     the end of the list. For example, with
     ```c++
     class A {};
     class B : public A {};
     class C : public B {};
     ```
     A cast from `C` to `A` will be [Cderived2base ["::B";"::A"]] and
       the "::C" comes from the type of the sub-expression.
     A cast from `A` to `C` will be [Cbase2derived ["::B";"::A"]] and
       the "::C" comes form the type of the expression.
   *)
| Cderived2base (_ : list globname)
| Cbase2derived (_ : list globname)
| Cintegral
| Cint2bool
| Cfloat2int
| Cnull2ptr
| Cbuiltin2fun
| Cctor
| C2void
| Cuser        (conversion_function : obj_name)	(** TODO (FM-3431): Consider just emitting the method call *)
| Creinterpret (_ : type)
| Cstatic      (_ : Cast')
| Cdynamic     (from to : globname)
| Cconst       (_ : type).
#[global] Arguments Cast' _ : clear implicits, assert.
(**
TODO (FM-3431): For the explicit casts, we could embed the type as
written and compute the value category (rather than annote `Ecast`
with a value category).
*)
#[global] Instance Cast_eq_dec {type : Set} `{!EqDecision type} : EqDecision (Cast' type).
Proof. solve_decision. Defined.
Notation Cast := (Cast' type).

(** * References *)
Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).
#[global] Instance: EqDecision VarRef.
Proof. solve_decision. Defined.

Variant call_type : Set := Virtual | Direct.
#[global] Instance: EqDecision call_type.
Proof. solve_decision. Defined.

Variant ValCat : Set := Lvalue | Prvalue | Xvalue.
#[global] Instance: EqDecision ValCat.
Proof. solve_decision. Defined.
#[global] Instance ValCat_countable : Countable ValCat.
Proof.
  apply (inj_countable
    (fun vc => match vc with Lvalue => 1 | Prvalue => 2 | Xvalue => 3 end)
    (fun n =>
    match n with
    | 1 => Some Lvalue
    | 2 => Some Prvalue
    | 3 => Some Xvalue
    | _ => None
    end)
  )%positive.
  abstract (by intros []).
Defined.

Variant OffsetInfo : Set :=
  | Oo_Field (_ : field).
#[global] Instance: EqDecision OffsetInfo.
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
| Eread_ref (e : Expr) (* type = type_of e *)
| Ederef (e : Expr) (_ : type) (* XXX type = strip [Tptr] from [type_of e] *)
| Eaddrof (e : Expr) (* type = Tptr (type_of e) *)
| Eassign (e _ : Expr) (_ : type) (* XXX type = type_of e *)
| Eassign_op (_ : BinOp) (e _ : Expr) (_ : type) (* XXX = type_of e *)
  (* ^ these are specialized because they are common *)

| Epreinc (_ : Expr) (_ : type)
| Epostinc (_ : Expr) (_ : type)
| Epredec (_ : Expr) (_ : type)
| Epostdec (_ : Expr) (_ : type)
  (* ^ special unary operators *)

| Eseqand (_ _ : Expr) (* type = Tbool *)
| Eseqor  (_ _ : Expr) (* type = Tbool *)
| Ecomma (e1 e2 : Expr) (* type = type_of e2 *)
  (* ^ these are specialized because they have special control flow semantics *)

| Ecall    (_ : Expr) (_ : list Expr) (_ : type)
| Ecast    (_ : Cast) (e : Expr) (_ : ValCat) (_ : type)

| Emember  (obj : Expr) (_ : field) (_ : type)
  (* TODO: maybe replace the left branch use [Expr] here? *)
| Emember_call (method : (obj_name * call_type * type) + Expr) (obj : Expr) (_ : list Expr) (_ : type)

| Esubscript (_ : Expr) (_ : Expr) (_ : ValCat) (_ : type)
| Esize_of (_ : type + Expr) (_ : type)
| Ealign_of (_ : type + Expr) (_ : type)
| Eoffset_of (_ : OffsetInfo) (_ : type)
| Econstructor (_ : obj_name) (_ : list Expr) (_ : type)
| Eimplicit (_ : Expr)
| Eimplicit_init (_ : type)
| Eif       (_ _ _ : Expr) (_ : ValCat) (_ : type)

| Ethis (_ : type)
| Enull
| Einitlist (_ : list Expr) (_ : option Expr) (_ : type)

| Enew (new_fn : obj_name * type) (new_args : list Expr)
       (alloc_ty : type)
       (array_size : option Expr) (init : option Expr) (* type = Tptr alloc_ty *)
| Edelete (is_array : bool) (del_fn : obj_name * type)
          (* When [deleted_type] is a class with a [virtual] destructor and the
             most derived class has an [operator delete], [del_fn] will be
             ignored. *)
          (arg : Expr) (deleted_type : type) (* type = Tvoid *)

| Eandclean (_ : Expr)
| Ematerialize_temp (_ : Expr) (_ : ValCat)

| Eatomic (_ : AtomicOp) (_ : list Expr) (_ : type)
| Eva_arg (_ : Expr) (_ : type)
| Epseudo_destructor (_ : type) (_ : Expr)

| Earrayloop_init (oname : N) (src : Expr) (level : N) (length : N) (init : Expr) (_ : type)
| Earrayloop_index (level : N) (_ : type)
| Eopaque_ref (name : N) (_ : ValCat) (_ : type)
| Eunsupported (_ : bs) (_ : ValCat) (_ : type)
.
Notation MethodRef := ((obj_name * call_type * type) + Expr)%type (only parsing).

#[global] Instance Expr_eq_dec : EqDecision Expr.
Proof.
  rewrite /RelDecision /Decision.
  fix IHe 1.
  rewrite -{1}/(EqDecision Expr) in IHe.
  decide equality; try solve_trivial_decision.
Defined.

Definition Edefault_init_expr (e : Expr) : Expr := e.
