Require Import Coq.Strings.String.

Definition name : Set := string.
Definition globname : Set := name.
Definition localname : Set := name.

Variant value : Set :=
| LitVal (_ : nat).
Definition addr : Set := value.
Definition addr_to_value : addr -> value := fun x => x.
Coercion addr_to_value : addr >-> value.
Coercion LitVal : nat >-> value.


Definition field : Set := string.
Inductive type : Set :=
| Tpointer (_ : type)
| Treference (_ : type)
| Tint (size : option nat) (signed : bool)
| Tchar (size : option nat) (signed : bool)
| Tvoid
| Tunknown.


Record TypeInfo : Set :=
{ alignment : nat
; size : nat
; offset : list (field * nat)
}.

Class Ctxt :  Type :=
{ resolve_glob : globname -> option addr
; type_info : type -> option TypeInfo
}.


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
.

Definition BinOp : Set := string.


Require Import Coq.ZArith.BinIntDef.

Inductive Expr : Set :=
| Evar     (_ : name)
| Eload    (_ : Expr)
| Ebinop   (_ : BinOp) (_ _ : Expr)
(*| Eaddr_of (_ : Expr) *)
| Eint     (_ : Z) (_ : type)
| Ebool    (_ : bool)
| Ecall    (_ : Expr) (_ : list Expr)
| Ecast    (_ : Cast) (_ : Expr)
| Emember  (_ : Expr) (_ : type) (_ : field)
| Esize_of (_ : type + Expr)
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
| Dstruct (_ : name) (fields : list (name * type))
| Denum   (_ : name) (_ : option type) (branches : list (name * Expr))
          (* the initializers need to be constant expressions *)
| Dempty
  (* ^ this will be erased *)
| Dnamespace (_ : name) (_ : Decl)
  (* ^ this will be erased *)
.

Coercion Sexpr : Expr >-> Stmt.
