Require Import Coq.NArith.BinNat.
Require Import Coq.Strings.String.

Set Primitive Projections.

Definition ident : Set := string.

Record globname : Set :=
{ g_path : list ident
; g_name : ident
}.
Definition localname : Set := ident.

Record field : Set :=
{ f_type : globname (* name of struct or class *)
; f_name : ident
}.
Record type_qualifiers : Set :=
{ q_const : bool
; q_volatile : bool }.

Inductive type : Set :=
| Tpointer (_ : type)
| Treference (_ : type)
| Tint (size : option nat) (signed : bool)
| Tchar (size : option nat) (signed : bool)
| Tvoid
| Tunknown
| Tarray (_ : type) (_ : option nat)
| Tref (_ : globname)
| Tfunction (_ : type) (_ : list type)
| Tqualified (_ : type_qualifiers) (_ : type)
| Tbool.


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

Variant Cast : Set :=
| Cbitcast
| Clvaluebitcast
| Cl2r
| Cnoop
| Carray2pointer
| Cfunction2pointer
| Cint2pointer
| Cpointer2int
| Cderived2base
| Cintegral
| Cint2bool
| Cnull2ptr
| Cbuiltin2function
| Cconstructorconversion
.

Definition UnOp : Set := string.
Definition BinOp : Set := string.

Require Import Coq.ZArith.BinIntDef.

Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).

Inductive Expr : Set :=
| Evar     (_ : VarRef)
| Eload    (_ : Expr)
| Eunop    (_ : UnOp) (_ : Expr)
| Ebinop   (_ : BinOp) (_ _ : Expr)

| Eint     (_ : Z) (_ : type)
| Ebool    (_ : bool)
| Ecall    (_ : Expr) (_ : list Expr)
| Ecast    (_ : Cast) (_ : Expr)

| Emember  (_ : Expr) (_ : field)
| Emember_call (_ : globname) (obj : Expr) (_ : list Expr)

| Esubscript (_ : Expr) (_ : Expr)
| Esize_of (_ : type + Expr)
| Econstructor (_ : globname) (_ : list Expr)
| Eimplicit (_ : Expr)
| Eif       (_ _ _ : Expr)
| Ethis
| Enull
| Einitlist (_ : list Expr)
.

Inductive Stmt : Set :=
| Sskip
| Sseq    (_ : list Stmt)
| Sdecl   (_ : list (ident * type * option Expr))

| Sif     (_ : option (ident * type * option Expr)) (_ : Expr) (_ _ : Stmt)
| Swhile  (_ : Expr) (_ : Stmt)
| Sfor    (_ : option Stmt) (_ _ : option Expr) (_ : Stmt)

| Sreturn (_ : option Expr)

| Sexpr   (_ : Expr)

| Sasm (_ : string)
.

Variant OrDefault {t : Set} : Set :=
| Default
| UserDefined (_ : t).
Arguments OrDefault : clear implicits.

Record Ctor : Set :=
{ c_params : list (ident * type)
; c_body   : option (OrDefault Stmt)
}.

Record Func : Set :=
{ f_return : type
; f_params : list (ident * type)
; f_body   : option Stmt
}.

Record Struct {Decl : Set} : Set :=
{ s_bases : list globname
  (* ^ base classes *)
; s_fields : list (ident * type * option Expr)
  (* ^ fields (with optional initializers *)
; s_ctors : list Ctor
  (* ^ constructors *)
; s_dtor  : option (OrDefault Stmt)
  (* ^ destructor *)
; s_nested  : list Decl
  (* ^ non-members, e.g. nested types, static functions, etc. *)
}.
Arguments Struct : clear implicits.


(* global declarations *)
Inductive Decl : Set :=
| Dvar         (_ : ident) (_ : type) (_ : option Expr)
| Dtypedef     (_ : ident) (_ : type)

| Dfunction    (_ : ident) (_ : Func)
| Dmethod      (_ : ident) (_ : globname) (_ : Func)

| Dstruct      (_ : ident) (_ : Struct Decl)
  (* ^ structures & classes *)

| Denum        (_ : ident) (_ : option type) (branches : list (ident * option Expr))
  (* ^ enumerations (the initializers need to be constant expressions) *)
| Dnamespace   (_ : ident) (_ : list Decl)
  (* ^ this will be erased *)
| Dexterns                 (_ : list Decl)
| Dtemplate_function       (_ : Decl) (instantiations : list Decl)
  (* ^ right now this just expands the template, it should change *)
.




Coercion Sexpr : Expr >-> Stmt.

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

(* note(gmm): types without explicit size information need to
 * be parameters of the underlying code, otherwise we can't
 * describe the semantics correctly.
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
