Require Import Coq.Strings.String.

Definition name : Set := string.
Record globname : Set :=
{ g_path : list name
; g_name : name
}.
Definition localname : Set := name.

Record field : Set :=
{ f_type : globname
; f_name : name
}.
Inductive type : Set :=
| Tpointer (_ : type)
| Treference (_ : type)
| Tint (size : option nat) (signed : bool)
| Tchar (size : option nat) (signed : bool)
| Tvoid
| Tunknown
| Tarray (_ : type) (_ : option nat)
| Tref (_ : globname)
| Tfunction (_ : type) (_ : list type).


Record TypeInfo : Set :=
{ alignment : nat
; size : nat
; offset : list (field * nat)
}.

(*
Class Ctxt :  Type :=
{ resolve_glob : globname -> option addr
; type_info : type -> option TypeInfo
}.
*)


Inductive op : Set :=
| Add | Sub | Mul.

Variant Cast : Set :=
| Cbitcast
| Clvaluebitcast
| Cl2r
| Cnoop
| Carray2pointer
| Cfunction2pointer
| Cint2ptr
| Cptr2int
| Cderived2base
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
(*| Eaddr_of (_ : Expr) *)
| Eint     (_ : Z) (_ : type)
| Ebool    (_ : bool)
| Ecall    (_ : Expr) (_ : list Expr)
| Ecast    (_ : Cast) (_ : Expr)
| Emember  (_ : Expr) (_ : field)
| Esubscript (_ : Expr) (_ : Expr)
| Esize_of (_ : type + Expr)
| Econstructor (_ : globname) (_ : list Expr)
| Emember_call (_ : globname) (obj : Expr) (_ : list Expr)
| Eimplicit (_ : Expr)
| Eif       (_ _ _ : Expr)
.

Inductive Stmt : Set :=
| Sskip
| Sseq    (_ : list Stmt)
| Sdecl   (_ : list (name * type * option Expr))

| Sif     (_ : Expr) (_ _ : Stmt)
| Swhile  (_ : option unit) (_ : Stmt) (_ : Stmt)


| Sreturn (_ : option Expr)

| Sexpr   (_ : Expr)
.

(* global declarations *)
Inductive Decl : Set :=
| Dvar (_ : name) (_ : type) (_ : option Expr)
| Dtypedef (_ : name) (_ : type)
| Dfunction (_ : name) (_ : list (name * type)) (_ : type) (_ : option Stmt)
| Dconstructor (_ : list (name * type)) (_ : option Stmt)
| Ddestructor (_ : option Stmt)
| Dstruct (_ : name) (bases : list globname) (fields : list (name * type)) (methods : list Decl)
| Denum   (_ : name) (_ : option type) (branches : list (name * Expr))
          (* the initializers need to be constant expressions *)
| Dempty
  (* ^ this will be erased *)
| Dnamespace (_ : name) (_ : Decl)
  (* ^ this will be erased *)
.

Coercion Sexpr : Expr >-> Stmt.


Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Notation "a !:: b" := (a :: b) (at level 30).
Local Open Scope string_scope.
Import ListNotations.

Definition T_int128 := Tint (Some 128) true.
Definition T_uint128 := Tint (Some 128) false.
Definition T_schar : type := Tchar None true.
Definition T_uchar : type := Tchar None false.
Definition T_int := Tint None true.

Definition NStop : list name := nil.