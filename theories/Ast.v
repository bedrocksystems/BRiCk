(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Strings.String.

Set Primitive Projections.

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

(*
Record globname : Set :=
{ g_path : list ident
; g_name : ident
}.
Parameter to_obj_name : globname -> obj_name.
*)

Definition localname : Set := ident.

Record field : Set :=
{ f_type : globname (* name of struct or class *)
; f_name : ident
}.
Record type_qualifiers : Set :=
{ q_const : bool
; q_volatile : bool }.

Definition merge_tq (a b : type_qualifiers) : type_qualifiers :=
  {| q_const := a.(q_const) || b.(q_const)
   ; q_volatile := a.(q_volatile) || b.(q_volatile)
   |}.

Inductive type : Set :=
| Tpointer (_ : type)
| Treference (_ : type)
| Trv_reference (_ : type)
| Tint (size : option nat) (signed : bool)
| Tchar (size : option nat) (signed : bool)
| Tvoid
| Tarray (_ : type) (_ : nat) (* unknown sizes are represented by pointers *)
| Tref (_ : globname)
| Tfunction (_ : type) (_ : list type)
| Tbool
| Tqualified (_ : type_qualifiers) (_ : type)
.

Fixpoint erase_qualifiers (t : type) : type :=
  match t with
  | Tpointer t => Tpointer (erase_qualifiers t)
  | Treference t => Treference (erase_qualifiers t)
  | Trv_reference t => Trv_reference (erase_qualifiers t)
  | Tint _ _
  | Tchar _ _
  | Tbool
  | Tvoid
  | Tref _ => t
  | Tarray t sz => Tarray (erase_qualifiers t) sz
  | Tfunction t ts => Tfunction (erase_qualifiers t) (List.map erase_qualifiers ts)
  | Tqualified _ t => erase_qualifiers t
  end.

Fixpoint drop_qualifiers (t : type) : type :=
  match t with
  | Tqualified _ t => drop_qualifiers t
  | _ => t
  end.

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

Class Ctxt :  Type :=
{ resolve_glob : globname -> option addr
; type_info : type -> option TypeInfo
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
.

Variant Cast : Set :=
| CCcast (_ : PrimCast)
| Cuser (conversion_function : globname)
| Creinterpret (_ : type)
| Cstatic      (_ : type)
| Cdynamic     (_ : type)
| Cconst       (_ : type)
.

Variant UnOp : Set :=
| Uminus
| Unot
| Ubnot
| Uother (_ : string).
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

Require Import Coq.ZArith.BinIntDef.

Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).

Variant ValCat : Set := Lvalue | Rvalue | Xvalue.

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
| Ecast    (_ : Cast) (_ : Expr) (_ : type)

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
| Etemp (_ : Expr) (_ : type)
.

Variant SwitchBranch : Set :=
| Default
| Exact (_ : Expr)
| Range (_ _ : Expr)
.

Inductive Stmt : Set :=
| Sseq    (_ : list Stmt)
| Sdecl   (_ : list (ident * type * option Expr))

| Sif     (_ : option (ident * type * option Expr)) (_ : Expr) (_ _ : Stmt)
| Swhile  (_ : option (ident * type * option Expr)) (_ : Expr) (_ : Stmt)
| Sfor    (_ : option Stmt) (_ : option Expr) (_ : option (ValCat * Expr)) (_ : Stmt)
| Sdo     (_ : Stmt) (_ : Expr)

| Sswitch (_ : Expr) (_ : list (SwitchBranch * Stmt))

| Sbreak
| Scontinue

| Sreturn (_ : option (ValCat * Expr))

| Sexpr   (_ : ValCat) (_ : Expr)

| Sasm (_ : string)
.

Variant OrDefault {t : Set} : Set :=
| Defaulted
| UserDefined (_ : t).
Arguments OrDefault : clear implicits.

Variant FieldOrBase {f b : Set} : Set :=
| Base (_ : b)
| Field (_ : f).
Arguments FieldOrBase : clear implicits.

Record Ctor : Set :=
{ c_class  : globname
; c_params : list (ident * type)
; c_body   : option (OrDefault (list (FieldOrBase ident globname * Expr) * Stmt))
}.

Record Dtor : Set :=
{ d_class  : globname
; d_body   : option (OrDefault (Stmt * list (FieldOrBase ident globname * globname)))
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

Record Struct {Decl : Set} : Set :=
{ s_bases : list globname
  (* ^ base classes *)
; s_fields : list (ident * type * option Expr)
  (* ^ fields (with optional initializers) *)
(* ; s_ctors : list Ctor *)
(*   (* ^ constructors *) *)
(* ; s_dtor  : option  *)
(*   (* ^ destructor *) *)
(* ; s_nested : list Decl *)
(*   (* ^ non-members, e.g. nested types, static functions, etc. *) *)
}.
Arguments Struct : clear implicits.

Variant OrType {t : Set} : Set :=
| Typename
| NotType (_ : t).
Arguments OrType : clear implicits.

(* global declarations *)
Inductive Decl : Set :=
| Dvar         (name : obj_name) (_ : type) (_ : option Expr)
| Dtypedef     (name : globname) (_ : type)

| Dfunction    (name : obj_name) (_ : Func)
| Dmethod      (name : obj_name) (_ : Method)
| Dconstructor (name : obj_name) (_ : Ctor)
| Ddestructor  (name : obj_name) (_ : Dtor)

| Dstruct      (name : globname) (_ : option (Struct Decl))
  (* ^ structures & classes *)

| Denum        (name : globname) (_ : option type) (branches : list (ident * option Expr))
  (* ^ enumerations (the initializers need to be constant expressions) *)
| Dconstant    (name : globname) (_ : type) (_ : nat)
(*
| Dtemplated   (_ : list (OrType type * ident)) (_ : Decl)
               (instantiations : list Decl)
*)
  (* ^ right now this just expands the template, it should change *)
.

Definition module : Set :=
  list Decl.

Definition NStop : list ident := nil.

(* types with explicit size information
 *)
Definition T_int8 := Tint (Some 8) true.
Definition T_uint8 := Tint (Some 8) false.
Definition T_int16 := Tint (Some 16) true.
Definition T_uint16 := Tint (Some 16) false.
Definition T_int32 := Tint (Some 32) true.
Definition T_uint32 := Tint (Some 32) false.
Definition T_int64 := Tint (Some 64) true.
Definition T_uint64 := Tint (Some 64) false.
Definition T_int128 := Tint (Some 128) true.
Definition T_uint128 := Tint (Some 128) false.

Definition Sskip := Sseq nil.

(* note(gmm): types without explicit size information need to
 * be parameters of the underlying code, otherwise we can't
 * describe the semantics correctly.
 * - cpp2v should probably insert these types.
 *)
Parameter T_ushort : type.
Parameter T_short : type.
Parameter T_long : type.
Parameter T_ulong : type.
Parameter T_ulonglong : type.
Parameter T_longlong : type.
Parameter T_uint : type.

Definition T_schar : type := Tchar None true.
Definition T_uchar : type := Tchar None false.
Definition T_int := Tint None true.

Coercion CCcast : PrimCast >-> Cast.