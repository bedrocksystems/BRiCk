(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.NArith.BinNatDef.
From Coq.Strings Require Import
     Ascii String.
Require Import Coq.ZArith.BinIntDef.

Require Import Cpp.Util.

Set Primitive Projections.

Local Open Scope N_scope.


(* this represents names that exist in object files. *)
Definition obj_name : Set := string.

Definition ident : Set := string.

(* naming in C++ is complex.
 * - everything has a path, e.g. namespaces, classes, etc.
 *   examples: ::foo         -- the namespace `foo`
 *             ::Foo         -- the class/struct/enum `Foo`
 *             ::Foo<int, 1> -- templated class (template parameters are types *and* expressions)
 * - functions (but not variables) can be overloaded.
 *   (this is addressed via name mangling)
 * - types (classes, structs, typedefs, etc) are not mangled because they are
 *   not present in the object file
 * - there are also "unnamed" functions, e.g. constructors and destructors
 *)
Definition globname : Set := string.
  (* these are mangled names. for consistency, we're going to
   * mangle everything.
   *)
Global Instance Decidable_eq_globname : forall a b : globname, Decidable (a = b) :=
  Decidable_eq_string.

(* local names *)
Definition localname : Set := ident.

Global Instance Decidable_eq_localname : forall a b : localname, Decidable (a = b) :=
  Decidable_eq_string.

Record field : Set :=
{ f_type : globname (* name of struct or class *)
; f_name : ident
}.
Global Instance Decidable_eq_field (a b : field) : Decidable (a = b).
Proof.
refine
  {| Decidable_witness :=
       decide (a.(f_type) = b.(f_type)) && decide (a.(f_name) = b.(f_name))
   ; Decidable_spec := _ |}.
  rewrite Bool.andb_true_iff. repeat rewrite decide_ok.
  destruct a, b; simpl; split; firstorder congruence.
Defined.

Record type_qualifiers : Set :=
{ q_const : bool
; q_volatile : bool }.
Global Instance Decidable_eq_type_qualifiers (a b : type_qualifiers) : Decidable (a = b).
Proof.
refine
  {| Decidable_witness := decide (a.(q_const) = b.(q_const)) && decide (a.(q_volatile) = b.(q_volatile))
   |}.
rewrite Bool.andb_true_iff. repeat rewrite decide_ok.
destruct a; destruct b; simpl; firstorder; congruence.
Defined.

Definition merge_tq (a b : type_qualifiers) : type_qualifiers :=
  {| q_const := a.(q_const) || b.(q_const)
   ; q_volatile := a.(q_volatile) || b.(q_volatile)
   |}.

Definition size : Set := N.

Bind Scope N_scope with size.

Variant signed : Set := Signed | Unsigned.

Inductive type : Set :=
| Tpointer (_ : type)
| Treference (_ : type)
| Trv_reference (_ : type)
| Tint (size : size) (signed : signed)
| Tchar (size : size) (signed : signed)
| Tvoid
| Tarray (_ : type) (_ : N) (* unknown sizes are represented by pointers *)
| Tref (_ : globname)
| Tfunction (_ : type) (_ : list type)
| Tbool
| Tqualified (_ : type_qualifiers) (_ : type)
.
Definition Talias (underlying : type) (name : globname) : type :=
  underlying.
Definition type_eq_dec : forall (ty1 ty2 : type), { ty1 = ty2 } + { ty1 <> ty2 }.
Proof.
  fix IHty1 1.
  repeat (decide equality).
Defined.
Global Instance Decidable_eq_type (a b : type) : Decidable (a = b) :=
  dec_Decidable (type_eq_dec a b).

Definition Qconst_volatile : type -> type :=
  Tqualified {| q_const := true ; q_volatile := true |}.
Definition Qconst : type -> type :=
  Tqualified {| q_const := true ; q_volatile := false |}.
Definition Qmut_volatile : type -> type :=
  Tqualified {| q_const := false ; q_volatile := true |}.
Definition Qmut : type -> type :=
  Tqualified {| q_const := false ; q_volatile := false |}.

(*
Record TypeInfo : Set :=
{ alignment : nat
; size : nat
; offset : list (field * nat)
}.
*)

Variant PrimCast : Set :=
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
| Cintegral
| Cint2bool
| Cnull2ptr
| Cbuiltin2function
| Cconstructorconversion
| C2void
.
Global Instance Decidable_eq_PrimCast (a b : PrimCast) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality) : {a = b} + {a <> b}).

Variant Cast : Set :=
| CCcast       (_ : PrimCast)
| Cuser        (conversion_function : obj_name)
| Creinterpret (_ : type)
| Cstatic      (from to : globname)
| Cdynamic     (from to : globname)
| Cconst       (_ : type)
.
Global Instance Decidable_eq_Cast (a b : Cast) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).


Variant UnOp : Set :=
| Uminus
| Unot
| Ubnot
| Uother (_ : string).
Global Instance Decidable_eq_UnOp (a b : UnOp) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).

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
.
Global Instance Decidable_eq_BinOp (a b : BinOp) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).

Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).
Global Instance Decidable_eq_VarRef (a b : VarRef) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).


Variant ValCat : Set := Lvalue | Rvalue | Xvalue.
Global Instance Decidable_eq_ValCat (a b : ValCat) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).


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
Global Instance Decidable_eq_AtomicOp (a b : AtomicOp) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).

Inductive Expr : Set :=
| Econst_ref (_ : VarRef) (_ : type)
  (* ^ these are different because they do not have addresses *)
| Evar     (_ : VarRef) (_ : type)
  (* ^ local variable reference *)

| Echar    (_ : Ascii.ascii) (_ : type)
| Estring  (_ : String.string) (_ : type)
| Eint     (_ : Z) (_ : type)
| Ebool    (_ : bool)
  (* ^ literals *)

| Eunop    (_ : UnOp) (_ : Expr) (_ : type)
| Ebinop   (_ : BinOp) (_ _ : Expr) (_ : type)
 (* ^ note(gmm): overloaded operators are already resolved. so an overloaded
  * operator shows up as a function call, not a `Eunop` or `Ebinop`.
  * this includes the assignment operator for classes.
  *)
| Ederef (_ : Expr) (_ : type)
| Eaddrof (_ : Expr) (_ : type)
| Eassign (_ _ : Expr) (_ : type)
| Eassign_op (_ : BinOp) (_ _ : Expr) (_ : type)
  (* ^ these are specialized because they are common *)

| Epreinc (_ : Expr) (_ : type)
| Epostinc (_ : Expr) (_ : type)
| Epredec (_ : Expr) (_ : type)
| Epostdec (_ : Expr) (_ : type)
  (* ^ special unary operators *)

| Eseqand (_ _ : Expr) (_ : type)
| Eseqor  (_ _ : Expr) (_ : type)
| Ecomma (vc : ValCat) (_ _ : Expr) (_ : type)
  (* ^ these are specialized because they have special control flow semantics *)

| Ecall    (_ : Expr) (_ : list (ValCat * Expr)) (_ : type)
| Ecast    (_ : Cast) (_ : ValCat * Expr) (_ : type)

| Emember  (obj : Expr) (_ : field) (_ : type)
| Emember_call (is_virtual : bool) (method : globname) (obj : Expr) (_ : list (ValCat * Expr)) (_ : type)

| Esubscript (_ : Expr) (_ : Expr) (_ : type)
| Esize_of (_ : type + Expr) (_ : type)
| Ealign_of (_ : type + Expr) (_ : type)
| Econstructor (_ : globname) (_ : list (ValCat * Expr)) (_ : type)
| Eimplicit (_ : Expr) (_ : type)
| Eif       (_ _ _ : Expr) (_ : type)

| Ethis (_ : type)
| Enull
| Einitlist (_ : list Expr) (_ : type)

| Enew (_ : option globname) (array_size : option Expr) (init : option Expr) (_ : type)
| Edelete (is_array : bool) (_ : option globname) (_ : Expr) (_ : type)

| Eandclean (_ : Expr) (_ : type)
| Ematerialize_temp (_ : Expr) (_ : type)

| Eatomic (_ : AtomicOp) (_ : list (ValCat * Expr)) (_ : type)

| Eva_arg (_ : Expr) (_ : type)
| Eunsupported (_ : string) (_ : type)
.

Definition Edefault_init_expr (e : Expr) : Expr := e.

Variant SwitchBranch : Set :=
| Exact (_ : Z)
| Range (_ _ : Z)
.

Inductive Stmt : Set :=
| Sseq    (_ : list Stmt)
| Sdecl   (_ : list (ident * type * option Expr))

| Sif     (_ : option (ident * type * option Expr)) (_ : Expr) (_ _ : Stmt)
| Swhile  (_ : option (ident * type * option Expr)) (_ : Expr) (_ : Stmt)
| Sfor    (_ : option Stmt) (_ : option Expr) (_ : option (ValCat * Expr)) (_ : Stmt)
| Sdo     (_ : Stmt) (_ : Expr)

| Sswitch (_ : Expr) (_ : Stmt)
| Scase   (_ : SwitchBranch)
| Sdefault

| Sbreak
| Scontinue

| Sreturn (_ : option (ValCat * Expr))

| Sexpr   (_ : ValCat) (_ : Expr)

| Sattr (_ : list string) (_ : Stmt)

| Sasm (_ : string) (volatile : bool)
       (inputs : list (string * Expr))
       (outputs : list (string * Expr))
       (clobbers : list string)
.

Variant OrDefault {t : Set} : Set :=
| Defaulted
| UserDefined (_ : t).
Arguments OrDefault : clear implicits.

Variant FieldOrBase : Set :=
| Base (_ : globname)
| Field (_ : ident)
| Indirect (anon_path : list (ident * globname)) (_ : ident).

Record Ctor : Set :=
{ c_class  : globname
; c_params : list (ident * type)
; c_body   : option (OrDefault (list (FieldOrBase * Expr) * Stmt))
}.

Record Dtor : Set :=
{ d_class  : globname
; d_body   : option (OrDefault (Stmt * list (FieldOrBase * obj_name)))
}.

Record Func : Set :=
{ f_return : type
; f_params : list (ident * type)
; f_body   : option Stmt
}.

Record Method : Set :=
{ m_return  : type
; m_class   : globname
; m_this_qual : type_qualifiers
; m_params  : list (ident * type)
; m_body    : option Stmt
}.

Record Union : Set :=
{ u_fields : list (ident * type * option Expr)
  (* ^ fields (with optional initializers) *)
}.

Record Struct : Set :=
{ s_bases : list globname
  (* ^ base classes *)
; s_fields : list (ident * type * option Expr)
  (* ^ fields (with optional initializers) *)
}.

Variant Ctor_type : Set := Ct_Complete | Ct_Base | Ct_Comdat.

(* Definition ctor_name (type : Ctor_type) (cls : globname) : obj_name := *)
(*   match cls with *)
(*   | String _ (String _ s) => *)
(*     "_ZN" ++ s ++ "C" ++ (match type with *)
(*                           | Ct_Complete => "1" *)
(*                           | Ct_Base => "2" *)
(*                           | Ct_Comdat => "5" *)
(*                           end) ++ "Ev" *)
(*   | _ => "" *)
(*   end%string. *)

Variant Dtor_type : Set := Dt_Deleting | Dt_Complete | Dt_Base | Dt_Comdat.

Definition dtor_name (type : Dtor_type) (cls : globname) : obj_name :=
  match cls with
  | String _ (String _ s) =>
    "_ZN" ++ s ++ "D" ++ ("0" (*match type with
                          | Dt_Deleting => "0"
                          | Dt_Complete => "1"
                          | Dt_Base => "2"
                          | Dt_Comdat => "5"
                          end *)) ++ "Ev"
  | _ => ""
  end%string.




(*
(* global declarations *)
Variant Decl : Set :=
| Dvar         (name : obj_name) (_ : type) (_ : option Expr)

| Dfunction    (name : obj_name) (_ : Func)
| Dmethod      (name : obj_name) (_ : Method)
| Dconstructor (name : obj_name) (_ : Ctor)
| Ddestructor  (name : obj_name) (_ : Dtor)

| Dunion       (name : globname) (_ : option Union)
| Dstruct      (name : globname) (_ : option Struct)
  (* ^ structures & classes *)

| Denum        (name : globname) (_ : option type) (branches : list (ident * option Expr))
  (* ^ enumerations (the initializers need to be constant expressions) *)
| Dconstant    (name : globname) (_ : type) (_ : Expr)

| Dtypedef     (name : globname) (_ : type)
(*
| Dtemplated   (_ : list (OrType type * ident)) (_ : Decl)
               (instantiations : list Decl)
*)
  (* ^ right now this just expands the template, it should change *)
.

Definition module : Set :=
  list Decl.
*)

(* types with explicit size information
 *)
Definition T_int8    := Tint 8 Signed.
Definition T_uint8   := Tint 8 Unsigned.
Definition T_int16   := Tint 16 Signed.
Definition T_uint16  := Tint 16 Unsigned.
Definition T_int32   := Tint 32 Signed.
Definition T_uint32  := Tint 32 Unsigned.
Definition T_int64   := Tint 64 Signed.
Definition T_uint64  := Tint 64 Unsigned.
Definition T_int128  := Tint 128 Signed.
Definition T_uint128 := Tint 128 Unsigned.

Definition Sskip := Sseq nil.

(* note(gmm): types without explicit size information need to
 * be parameters of the underlying code, otherwise we can't
 * describe the semantics correctly.
 * - cpp2v should probably insert these types.
 *)
(**
https://en.cppreference.com/w/cpp/language/types
The 4 definitions below use the LP64 data model.
LLP64 and LP64 agree except for the [long] type: see
the warning below.
In future, we may want to parametrize by a data model, or
the machine word size.
*)
Definition char_bits : size := 8.
Definition short_bits : size := 16.
Definition int_bits : size := 32.
Definition long_bits : size := 64. (** warning: LLP64 model uses 32 *)
Definition long_long_bits : size := 64.

Definition T_ushort : type := Tint short_bits Unsigned.
Definition T_short : type := Tint short_bits Signed.
Definition T_ulong : type := Tint long_bits Unsigned.
Definition T_long : type := Tint long_bits Signed.
Definition T_ulonglong : type := Tint long_long_bits Unsigned.
Definition T_longlong : type := Tint long_long_bits Signed.
Definition T_uint : type := Tint int_bits Unsigned.
Definition T_int : type := Tint int_bits Signed.

Definition T_schar : type := Tchar char_bits Signed.
Definition T_uchar : type := Tchar char_bits Unsigned.

Coercion CCcast : PrimCast >-> Cast.
